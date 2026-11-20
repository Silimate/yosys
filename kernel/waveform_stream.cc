#include "kernel/waveform_stream.h"

#include <charconv>
#include <cerrno>
#include <cstring>
#include <stdexcept>

#if defined(YOSYS_ENABLE_SPAWN) && !defined(_WIN32)
#include <fcntl.h>
#include <signal.h>
#include <spawn.h>
#include <sys/wait.h>
#include <unistd.h>
extern char **environ;
#endif

USING_YOSYS_NAMESPACE

std::function<WaveformStream::Command()> WaveformStream::resolve_reader;

#if defined(YOSYS_ENABLE_SPAWN) && !defined(_WIN32)
namespace {
int wait_reader(int pid)
{
	int status;
	while (waitpid(pid, &status, 0) < 0) {
		if (errno != EINTR) return -1;
	}
	return WIFEXITED(status) ? WEXITSTATUS(status) : -1;
}
}
#endif

WaveformStream::WaveformStream(Command args, const std::vector<uint32_t> &handles)
{
#if defined(YOSYS_ENABLE_SPAWN) && !defined(_WIN32)
	const char *override = std::getenv("YOSYS_FSDB_READER");
	auto command = override && *override ? Command{override} : resolve_reader ? resolve_reader() : Command{"fsdb-reader"};
	if (command.empty()) throw std::runtime_error("Missing FSDB reader command");
	command.insert(command.end(), args.begin(), args.end());
	std::vector<char *> argv;
	for (auto &word : command) argv.push_back(&word[0]);
	argv.push_back(nullptr);

	// Spooling only the selection avoids pipe deadlocks and the argv size limit.
	std::unique_ptr<FILE, decltype(&fclose)> input(tmpfile(), fclose);
	if (!input) throw std::runtime_error("Cannot open waveform handle list");
	for (uint32_t id : handles)
		if (fprintf(input.get(), "%u\n", id) < 0) throw std::runtime_error("Cannot write waveform handle list");
	if (fseek(input.get(), 0, SEEK_SET)) throw std::runtime_error("Cannot rewind waveform handle list");

	int fds[2];
#ifdef __linux__
	int pipe_error = pipe2(fds, O_CLOEXEC);
#else
	int pipe_error = pipe(fds);
#endif
	if (pipe_error < 0) throw std::runtime_error("Cannot open waveform reader pipe");
	posix_spawn_file_actions_t actions;
	int err = posix_spawn_file_actions_init(&actions);
	if (!err) {
		if (!(err = posix_spawn_file_actions_adddup2(&actions, fileno(input.get()), STDIN_FILENO)) &&
		    !(err = posix_spawn_file_actions_adddup2(&actions, fds[1], STDOUT_FILENO)) &&
		    !(err = posix_spawn_file_actions_addclose(&actions, fds[0])) &&
		    !(err = posix_spawn_file_actions_addclose(&actions, fds[1])) &&
		    !(err = posix_spawn_file_actions_addclose(&actions, fileno(input.get()))))
			err = posix_spawnp(&pid, argv[0], &actions, nullptr, argv.data(), environ);
		posix_spawn_file_actions_destroy(&actions);
	}
	close(fds[1]);
	if (err) {
		close(fds[0]);
		throw std::runtime_error("Cannot start FSDB reader " + command.front() + ": " + strerror(err));
	}
	out = fdopen(fds[0], "r");
	if (!out) {
		close(fds[0]);
		kill(pid, SIGTERM);
		wait_reader(pid);
		throw std::runtime_error("Cannot read FSDB reader output");
	}
	fcntl(fds[0], F_SETFD, FD_CLOEXEC);
#else
	(void)args;
	(void)handles;
	throw std::runtime_error("An external waveform reader requires POSIX process support");
#endif
}

WaveformStream::~WaveformStream()
{
	if (out) fclose(out);
	free(buf);
#if defined(YOSYS_ENABLE_SPAWN) && !defined(_WIN32)
	if (pid > 0) {
		kill(pid, SIGTERM);
		wait_reader(pid);
	}
#endif
}

bool WaveformStream::line(std::string &value)
{
#if defined(YOSYS_ENABLE_SPAWN) && !defined(_WIN32)
	if (pid < 0) return false;
	ssize_t count;
	do {
		errno = 0;
		count = getline(&buf, &size, out);
		if (count < 0 && errno == EINTR) clearerr(out);
	} while (count < 0 && errno == EINTR);
	if (count >= 0) {
		if (!count || buf[count-1] != '\n') throw std::runtime_error("Incomplete waveform reader record");
		value.assign(buf, count - 1);
		return true;
	}
	if (ferror(out)) throw std::runtime_error("Error reading waveform stream");
	auto status = wait_reader(pid);
	pid = -1;
	if (status != 0) throw std::runtime_error("FSDB reader failed; see reader diagnostic above");
#else
	(void)value;
#endif
	return false;
}

bool WaveformStream::change(uint64_t &time, uint32_t &handle, std::string &value)
{
	if (!line(value)) return false;
	const char *end = value.data() + value.size();
	auto t = std::from_chars(value.data(), end, time);
	if (t.ec != std::errc() || t.ptr == end || *t.ptr != ' ' || time < previous)
		throw std::runtime_error("Invalid waveform event time");
	auto h = std::from_chars(t.ptr + 1, end, handle);
	if (h.ec != std::errc() || h.ptr == end || *h.ptr != ' ' || !handle || h.ptr + 1 == end)
		throw std::runtime_error("Invalid waveform event handle or value");
	value.erase(0, h.ptr + 1 - value.data());
	previous = time;
	return true;
}

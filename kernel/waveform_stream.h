// A subprocess that streams waveform declarations or selected value changes.
#ifndef YOSYS_WAVEFORM_STREAM_H
#define YOSYS_WAVEFORM_STREAM_H

#include "kernel/yosys_common.h"
#include <cstdio>
#include <functional>

YOSYS_NAMESPACE_BEGIN

// --header FILE emits JSON arrays ["time", exponent, first_tick_string, last_tick_string]
// and ["var", id, scope, name, width, is_reg]. --changes FILE END reads decimal ids from
// stdin and emits "tick id bits" lines in time order through END (inclusive).
class WaveformStream {
public:
	using Command = std::vector<std::string>;
	static std::function<Command()> resolve_reader;

	WaveformStream(Command args, const std::vector<uint32_t> &handles = {});
	~WaveformStream();
	WaveformStream(const WaveformStream &) = delete;
	WaveformStream &operator=(const WaveformStream &) = delete;
	bool line(std::string &value);
	bool change(uint64_t &time, uint32_t &handle, std::string &value);

private:
	FILE *out = nullptr;
	int pid = -1;
	char *buf = nullptr;
	size_t size = 0;
	uint64_t previous = 0;
};

YOSYS_NAMESPACE_END
#endif

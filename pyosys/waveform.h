// Python bindings for waveform declarations and chronological FSDB changes.
#pragma once
#include "kernel/fstdata.h"

inline void bind_waveform(pybind11::module_ &m)
{
	namespace py = pybind11;
	using namespace Yosys;
	WaveformStream::resolve_reader = [] {
		py::gil_scoped_acquire gil;
		auto providers = py::module_::import("importlib.metadata").attr("entry_points")(
			py::arg("group") = "yosys.waveform_readers", py::arg("name") = "fsdb");
		for (auto provider : providers) {
			auto command = provider.attr("load")()();
			std::vector<std::string> argv;
			for (auto item : command) argv.push_back(py::cast<std::string>(item));
			return argv;
		}
		return WaveformStream::Command{"fsdb-reader"};
	};
	m.def("waveform_info", [](const std::string &filename) {
		FstData data(filename);
		py::list signals;
		for (const auto &v : data.getVars())
			signals.append(py::make_tuple(v.id, v.scope, v.name, v.width));
		return py::make_tuple(data.getScale(), data.getStartTime(), data.getEndTime(), signals);
	}, "Return the timescale exponent, time bounds and signal declarations.");
	py::class_<WaveformStream>(m, "FsdbChanges")
		.def(py::init([](const std::string &file, py::iterable ids, uint64_t end) {
			std::vector<uint32_t> handles;
			for (auto id : ids) handles.push_back(py::cast<uint32_t>(id));
			return std::make_unique<WaveformStream>(WaveformStream::Command{"--changes", file, std::to_string(end)}, handles);
		}))
		.def("__iter__", [](WaveformStream &self) -> WaveformStream & { return self; }, py::return_value_policy::reference_internal)
		.def("__next__", [](WaveformStream &self) {
			uint64_t time;
			uint32_t handle;
			std::string value;
			if (!self.change(time, handle, value)) throw py::stop_iteration();
			return py::make_tuple(time, handle, value);
		});
}

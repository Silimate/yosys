/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
 *
 *  Permission to use, copy, modify, and/or distribute this software for any
 *  purpose with or without fee is hereby granted, provided that the above
 *  copyright notice and this permission notice appear in all copies.
 *
 *  THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 *  WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 *  MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 *  ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 *  WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 *  ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 *  OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *
 *  ---
 *
 *  A simple and straightforward Verilog backend.
 *
 */

#ifndef VERILOG_BACKEND_H
#define VERILOG_BACKEND_H

#include <optional> // SILIMATE: kept_src
#include <string>

YOSYS_NAMESPACE_BEGIN
namespace VERILOG_BACKEND {

    const pool<string> &verilog_keywords();
    bool char_is_verilog_escaped(char c);
    bool id_is_verilog_escaped(const std::string &str);
    // SILIMATE: src less its entries starting with one of prefixes, for write_verilog and write_json -dropsrc
    std::optional<RTLIL::Const> kept_src(const RTLIL::Const &src, const std::vector<std::string> &prefixes);

}; /* namespace VERILOG_BACKEND */
YOSYS_NAMESPACE_END

#endif /* VERILOG_BACKEND_H */

// 宣言だけのヘッダ（実装は mem.cpp）
#pragma once
#include <systemc>
#include <tlm>
#include <tlm_utils/simple_target_socket.h>
#include "regs.h"

SC_MODULE(SplitMem) {
  tlm_utils::simple_target_socket<SplitMem> socket;
  uint32_t mem[MEM_WORDS];
  uint32_t errors;

  SC_CTOR(SplitMem);
  void b_transport(tlm::tlm_generic_payload& trans, sc_core::sc_time& delay);
  bool in_range(sc_dt::uint64 addr) const;
};

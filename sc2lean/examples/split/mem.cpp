#include <iostream>
#include "mem.h"

SplitMem::SplitMem(sc_core::sc_module_name nm) : socket("socket"), errors(0) {
  socket.register_b_transport(this, &SplitMem::b_transport);
}

bool SplitMem::in_range(sc_dt::uint64 addr) const {
  return addr < MEM_WORDS * 4;
}

void SplitMem::b_transport(tlm::tlm_generic_payload& trans, sc_core::sc_time& delay) {
  sc_dt::uint64 addr = trans.get_address();
  if (!in_range(addr)) {
    std::cout << "address error: " << addr << std::endl;
    SC_REPORT_WARNING("SplitMem", "address error");
    errors += 1;
    trans.set_response_status(tlm::TLM_ADDRESS_ERROR_RESPONSE);
    return;
  }
  sc_assert(trans.get_data_length() == 4);
  if (trans.is_read()) {
    memcpy(trans.get_data_ptr(), &mem[addr / 4], 4);
    delay += sc_core::sc_time(LAT_RD, sc_core::SC_NS);
  } else {
    memcpy(&mem[addr / 4], trans.get_data_ptr(), 4);
    delay += sc_core::sc_time(LAT_WR, sc_core::SC_NS);
  }
  trans.set_response_status(tlm::TLM_OK_RESPONSE);
}

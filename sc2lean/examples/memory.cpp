// LT ターゲット: ワード単位の SRAM
#include <systemc>
#include <tlm>
#include <tlm_utils/simple_target_socket.h>

SC_MODULE(Memory) {
  tlm_utils::simple_target_socket<Memory> socket;
  uint32_t mem[256];
  uint32_t reads;

  SC_CTOR(Memory) : socket("socket") {
    socket.register_b_transport(this, &Memory::b_transport);
    reads = 0;
    for (int i = 0; i < 256; ++i)
      mem[i] = 0;
  }

  void b_transport(tlm::tlm_generic_payload& trans, sc_core::sc_time& delay) {
    sc_dt::uint64 addr = trans.get_address();
    if (addr >= 1024 || trans.get_data_length() != 4) {
      trans.set_response_status(tlm::TLM_ADDRESS_ERROR_RESPONSE);
      return;
    }
    if (trans.get_command() == tlm::TLM_READ_COMMAND) {
      memcpy(trans.get_data_ptr(), &mem[addr / 4], 4);
      reads += 1;
      delay += sc_core::sc_time(20, sc_core::SC_NS);
    } else {
      memcpy(&mem[addr / 4], trans.get_data_ptr(), 4);
      delay += sc_core::sc_time(30, sc_core::SC_NS);
    }
    trans.set_response_status(tlm::TLM_OK_RESPONSE);
  }
};

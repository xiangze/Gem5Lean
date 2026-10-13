// 制約違反の例 2: switch 文、未登録の関数、b_transport 内の wait
#include <systemc>
#include <tlm>
#include <tlm_utils/simple_target_socket.h>

SC_MODULE(Bad2) {
  tlm_utils::simple_target_socket<Bad2> socket;
  uint32_t mode;

  SC_CTOR(Bad2) : socket("socket") {
    socket.register_b_transport(this, &Bad2::b_transport);
  }

  void b_transport(tlm::tlm_generic_payload& trans, sc_core::sc_time& delay) {
    switch (mode) {
      case 0: mode = 1; break;
      default: mode = 0;
    }
    wait(delay);
  }
};

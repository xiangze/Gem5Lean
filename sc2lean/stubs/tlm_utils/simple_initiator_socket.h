#pragma once
#include <tlm>
namespace tlm_utils {
  struct __sc2lean_fw_if {
    void b_transport(tlm::tlm_generic_payload&, sc_core::sc_time&);
  };
  template <class MODULE, unsigned int BUSWIDTH = 32>
  struct simple_initiator_socket {
    simple_initiator_socket();
    explicit simple_initiator_socket(const char*);
    __sc2lean_fw_if* operator->();
  };
}

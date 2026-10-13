#pragma once
#include <tlm>
namespace tlm_utils {
  template <class MODULE, unsigned int BUSWIDTH = 32>
  struct simple_target_socket {
    simple_target_socket();
    explicit simple_target_socket(const char*);
    void register_b_transport(MODULE*, void (MODULE::*)(tlm::tlm_generic_payload&, sc_core::sc_time&));
  };
}

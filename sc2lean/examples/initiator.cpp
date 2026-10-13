// LT イニシエータ: 0..3 番地に i*i を書き、読み戻して合計する
#include <systemc>
#include <tlm>
#include <tlm_utils/simple_initiator_socket.h>

SC_MODULE(Initiator) {
  tlm_utils::simple_initiator_socket<Initiator> socket;
  sc_core::sc_event done;
  uint32_t sum;
  uint32_t i;

  SC_CTOR(Initiator) : socket("socket") {
    SC_THREAD(run);
    sum = 0;
    i = 0;
  }

  void run() {
    tlm::tlm_generic_payload trans;
    sc_core::sc_time delay;
    uint32_t data;
    while (true) {
      data = i * i;
      trans.set_command(tlm::TLM_WRITE_COMMAND);
      trans.set_address(i * 4);
      trans.set_data_ptr(reinterpret_cast<unsigned char*>(&data));
      trans.set_data_length(4);
      delay = sc_core::SC_ZERO_TIME;
      socket->b_transport(trans, delay);
      wait(delay);

      trans.set_command(tlm::TLM_READ_COMMAND);
      delay = sc_core::SC_ZERO_TIME;
      socket->b_transport(trans, delay);
      wait(delay);
      sum += data;

      i = (i + 1) & 3;
      if (i == 0)
        done.notify(sc_core::sc_time(1, sc_core::SC_NS));
      wait(10, sc_core::SC_NS);
    }
  }
};

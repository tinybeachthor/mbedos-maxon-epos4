#if !defined (DEVICE_CAN) && !defined(DOXYGEN_ONLY)
#error CAN NOT SUPPORTED
#endif

#include "can.hpp"

#include <queue>

#include "debug.hpp"

/**
 * The default mbed CAN driver cannot be used in interrupt context because it
 * uses a Mutex lock. InterruptableCAN fixes this by disabling the Mutexlock.
 * This does mean that InterruptableCAN is NOT threadsafe.
 */
class InterruptableCAN : public mbed::CAN {
 public:
  InterruptableCAN (PinName rd, PinName td, int hz)
    : mbed::CAN(rd, td, hz) {};
  void lock() override {};
  void unlock() override {};
};

namespace can {

  constexpr long unsigned int SIZE = 30;
  rtos::Mail<CANMessage, SIZE> rx_buffer;

  InterruptableCAN* _bus;

  rtos::Semaphore tx_avail(1, 1);

  bool get (CANMessage& msg, uint32_t timeout = osWaitForever) {
    osEvent evt = rx_buffer.get(timeout);

    if (evt.status == osEventMail) {
      CANMessage* received = (CANMessage*)evt.value.p;
      memcpy(&msg, received, sizeof(CANMessage));

      if (rx_buffer.free(received)) {
        pc.printf("CAN_RX_FREE_FAIL\n");
      }

      return true;
    }
    else if (evt.status == osEventTimeout) {
      pc.printf("CAN_RX_TIMEOUT\n");
      return false;
    }

    pc.printf("CAN_RX_ERROR\n");
    return false;
  }

  bool put (const CANMessage& msg) {
    while (!_bus->write(msg)) {
      tx_avail.wait(1);
    }

    return true;
  }

  void read_irq () {
    CANMessage* msg = rx_buffer.alloc();

    if (msg == nullptr) {
      // if the buffer is full, drop the newly arrived message so we can keep running.
      CANMessage temp;
      _bus->read(temp);

      led_error = true;
    }
    else {
      // read msg and pass to rx_buffer
      _bus->read(*msg);

      if (rx_buffer.put(msg) != osOK) {
        // message was not passed properly
        led_error = true;
      }
    }
  }

  void write_irq () { tx_avail.release(); }

  void init (PinName rx, PinName tx, uint32_t baudrate = 500000) {
    EventQueue *queue = mbed_event_queue();

    _bus = new InterruptableCAN(rx, tx, baudrate),
    _bus->frequency(baudrate);

    _bus->attach(&read_irq, CAN::RxIrq);
    _bus->attach(&write_irq, CAN::TxIrq);
  }

}

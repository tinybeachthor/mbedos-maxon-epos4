#if !defined (DEVICE_CAN) && !defined(DOXYGEN_ONLY)
#error CAN NOT SUPPORTED
#endif

#include "can.hpp"
#include "mbed.h"

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

enum Priority : uint8_t {
  NORMAL   = 127,
  CRITICAL = 255,
};

struct CANMessagePriority {
  CANMessage msg;
  Priority priority;

  bool operator < (const CANMessagePriority& that) const {
    return (this->priority < that.priority);
  }
};

namespace can {

  constexpr long unsigned int SIZE = 30;
  rtos::Mail<CANMessage, SIZE> rx_buffer;

  std::priority_queue<CANMessagePriority> tx_queue;

  InterruptableCAN* _bus;

  rtos::Semaphore _lock(1);
  rtos::Semaphore tx_avail(1, 1);

  uint32_t rx_put_fail_count = 0;
  uint32_t rx_buffer_full_count = 0;

  bool get (CANMessage& msg, uint32_t millisec = osWaitForever) {
    osEvent evt = rx_buffer.get(millisec);

    if (evt.status == osEventMail) {
      CANMessage* received = (CANMessage*)evt.value.p;
      memcpy(&msg, received, sizeof(CANMessage));
      if (rx_buffer.free(received)) {
        can_warn(can::loom::SafetyMessage::Code_E::CAN_RX_FREE_FAIL);
      }
      return true;
    }
    else if (evt.status == osEventTimeout) {
      return false;
    }
  }

  bool put (const CANMessage& msg) {
    while (!_bus->write(msg)) {
      tx_avail.wait(1);
    }
    return true;
  }

  void read_irq () {
    CANMessage* msg = rx_buffer.alloc();

    // if the buffer is full, drop the newly arrived message so we can keep
    // running.
    if (msg == nullptr) {
      CANMessage temp;
      _bus->read(temp);
      // We don't (always) throw an explicit error because that will just
      // increase the load on the CAN bus and cause more errors.
      if (++rx_buffer_full_count % 100 == 99) {
        can_warn(can::loom::SafetyMessage::Code_E::CAN_RX_POOL_EMPTY);
      }
      return;
    }

    _bus->read(*msg);
    if (rx_buffer.put(msg) != osOK) {
      // We don't (always) throw an explicit error because that will just
      // increase the load on the CAN bus and cause more errors.
      if (++rx_put_fail_count % 100 == 99) {
        can_warn(can::loom::SafetyMessage::Code_E::CAN_RX_QUEUE_PUT_FAIL);
      }
    }
  }

  void write_irq () { tx_avail.release(); }

  void err_irq () { _bus->reset(); }

  void init (PinName rx, PinName tx, uint32_t baudrate = 500000) {
    _bus = new InterruptableCAN(rx, tx, baudrate),
    _bus->frequency(baudrate);

    _bus->attach(&read_irq, CAN::RxIrq);
    _bus->attach(&write_irq, CAN::TxIrq);
  }

} /* namespace can */

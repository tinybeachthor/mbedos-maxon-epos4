#pragma once

#include "mbed.h"

#include "can.hpp"

#include "debug.hpp"

class Epos4 {

public:
  Epos4 (PinName rx, PinName tx);

  void startPosMode ();
  void stop ();

private:

  /* CAN */
  Thread can_listener;
  void can_handler_routine () {
    while (true) {
      // wait for + handle CAN message (state transitions)

      CANMessage msg;
      can::get(msg, osWaitForever);
      pc.printf("Got CAN message : COB-ID=0x%X\n", msg.id);

      // HEARTBEAT (read NMT state)
      if (msg.id > 0x700) {
        uint8_t node_id = msg.id - 0x700;
        uint8_t state = *((uint8_t*)msg.data);
        pc.printf("Got HEARTBEAT from node#%d NMT state : %X\n", node_id, state);

        nmt_access.lock();
        nmt_current_state = state;
        nmt_cond->notify_all();
        nmt_access.unlock();
      }
    }
  }

  /* Heartbeat = NMT state

  Function code = 0x700 + NODE_ID

  Node's state in the first data byte.

  -----------------------------------------------------

  Automatically on boot
  Initialization -> Pre-Operational

  Pre-operational
    Emergency objects.
    Can be configured using SDO communication.
    NMT Protocol to transition state.

    NO PDO COMMUNICATION!

  Operational
    SDO, PDO, EMCY, NMT

  */
  enum nmt_state : uint8_t {
    BootUp = 0x00,
    Operational = 0x05,
    PreOperational = 0x7F,
    Stopped = 0x04,
  };

  Mutex nmt_access;
  ConditionVariable* nmt_cond;
  nmt_state nmt_current_state;

  void block_for_nmt_state(nmt_state desired_state) {
    nmt_access.lock();
    while (nmt_current_state != desired_state) {
      nmt_cond->wait();
    }
    nmt_access.unlock();
  }
};

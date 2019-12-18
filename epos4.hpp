#pragma once

#include "mbed.h"

#include "can.hpp"
#include "nmt_messages.hpp"
#include "epos4_messages.hpp"

#include "debug.hpp"

/**
  * CANOpen communication with Maxon EPOS4 Motorcontroller
  *
  * Assumptions:
  * - Expects sole control of a CAN bus with nothing, but a single EPOS4 connected.
  *
  */
class Epos4 {

public:
  Epos4 (PinName rx, PinName tx);

  void startPosMode ();
  void stop ();

private:

  const uint8_t NODE_ID = 0x00; // TODO set NODE_ID

  void quickStop ();

  // TODO ? watchdog for communication reset if no heartbeat for x

  /* CAN
  */
  Thread can_listener;
  void can_handler_routine () {
    // wait for + handle CAN messages
    while (true) {
      CANMessage msg;
      can::get(msg, osWaitForever);
      pc.printf("Got CAN message : COB-ID=0x%X\n", msg.id);

      // TRANSMIT SDO (data from slave)
      if (msg.id > 0x580) {
        uint8_t node_id = msg.id - 0x580;
        uint16_t index;
        memcpy(&index, msg.data + 1, 2);

        switch (index) {
          // STATUSWORD
          case 0x6041: {
            uint16_t data;
            memcpy(&data, msg.data + 4, 2);
            epos_state state = statuswordToState(data);

            pc.printf("Got STATUSWORD from node#%d EPOS state : %X\n", node_id, state);

            epos_access.lock();
            epos_current_state = state;
            epos_cond->notify_all();
            epos_access.unlock();
          }
          break;
        }
      }
      // HEARTBEAT (read NMT state)
      else if (msg.id > 0x700) {
        uint8_t node_id = msg.id - 0x700;
        uint8_t state = *((uint8_t*)msg.data);
        pc.printf("Got HEARTBEAT from node#%d NMT state : %X\n", node_id, state);

        nmt_access.lock();
        nmt_current_state = to_nmt_state(state);
        nmt_cond->notify_all();
        nmt_access.unlock();
      }
    }
  }

  /* epos state

  Read from STATUSWORD (x6041), Set with CONTROLWORD (0x6040)

  */
  enum epos_state : uint8_t {
    NotReadyToSwitchOn  = 0,
    SwitchOnDisabled    = 1,
    ReadyToSwitchOn     = 2,
    SwitchedOn          = 3,

    OperationEnabled    = 4,
    QuickStopActive     = 5,

    FaultReactionActive = 6,
    Fault               = 7,

    EPOS_Unknown        = 255,
  };

  epos_state statuswordToState(uint16_t statusword) {
    uint8_t lowByte = (uint8_t)(statusword & 0xFF);

    lowByte &= 0b01101111; // null 7 and 5 bits

    if (lowByte == 0b00000000)
      return NotReadyToSwitchOn;
    else if (lowByte == 0b01000000)
      return SwitchOnDisabled;
    else if (lowByte == 0b00100001)
      return ReadyToSwitchOn;
    else if (lowByte == 0b00100011)
      return SwitchedOn;
    else if (lowByte == 0b00100111)
      return OperationEnabled;
    else if (lowByte == 0b00000111)
      return QuickStopActive;
    else if (lowByte == 0b00001111)
      return FaultReactionActive;
    else if (lowByte == 0b00001000)
      return Fault;

    return EPOS_Unknown;
  }

  Mutex epos_access;
  ConditionVariable* epos_cond;
  epos_state epos_current_state = EPOS_Unknown;

  // TODO remove
  void poll_epos_state () {
    can::put(epos4_messages::statusword(NODE_ID));
  }

  void block_for_epos_state (epos_state desired) {
    pc.printf("Waiting for EPOS state : %d\n", desired);

    epos_access.lock();
    while (epos_current_state != desired) {
      epos_cond->wait();
      pc.printf("Received EPOS state : %d\n", epos_current_state);
    }
    epos_access.unlock();

    pc.printf("Attained EPOS state : %d\n", desired);
  }

  /* NMT state (HEARTBEAT COB-ID:0x700)

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

    NMT_Unknown = 0xFF,
  };

  Mutex nmt_access;
  ConditionVariable* nmt_cond;
  nmt_state nmt_current_state = NMT_Unknown;

  void block_for_nmt_state(nmt_state desired_state) {
    nmt_access.lock();
    while (nmt_current_state != desired_state) {
      nmt_cond->wait();
    }
    nmt_access.unlock();
  }

  nmt_state to_nmt_state (uint8_t state) {
    switch (state) {
      case BootUp: return BootUp;
      case PreOperational: return PreOperational;
      case Operational: return Operational;
      case Stopped: return Stopped;

      default: return NMT_Unknown;
    }
  }
};

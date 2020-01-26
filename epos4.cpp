#include "epos4.hpp"

CANMessage constructCANMessage (const uint8_t* raw, const uint8_t NODE_ID) {
  CANMessage out;
  out.format = CANStandard; // Standard format - 11bits
  out.id = 0x600 + NODE_ID; // Function code (RCV SDO) + NODE_ID
  memcpy(out.data, raw, 8);
  out.len = 8;

  return out;
}

Epos4::Epos4 (PinName rx, PinName tx)
  : epos_current_state(EPOS_Unknown)
  , nmt_current_state(NMT_Unknown)
{
  nmt_cond = new ConditionVariable(nmt_access);
  epos_cond = new ConditionVariable(epos_access);

  steering_can::init(rx, tx, 1000000);

  can_listener.start(callback(this, &Epos4::can_handler_routine));

  block_for_any_nmt_state();
  pc.printf("Go a nmt state\n");

  nmt_access.lock();
  Epos4::nmt_state state = nmt_current_state;
  nmt_access.unlock();

  pc.printf("State during pcb startup is : 0x%X\n", state);

  if (state == Operational || state == Stopped) {
    steering_can::put(nmt_messages::construct(nmt_messages::transition::ResetNode));
    ThisThread::sleep_for(50);
  }

  // Wait for first HEARTBEAT message to arrive
  block_for_nmt_state(nmt_state::PreOperational);
  pc.printf("Got to NMT PreOperational\n");

  // Go to NMT Operational
  steering_can::put(nmt_messages::construct(nmt_messages::Operational));
  block_for_nmt_state(nmt_state::Operational);
  pc.printf("Got to NMT Operational\n");
}

void Epos4::goToReadyState () {
  block_for_epos_state(SwitchOnDisabled);

  // Shutdown (-> ReadyToSwitchOn)
  steering_can::put(epos4_messages::constructControlword(epos4_messages::Shutdown, NODE_ID));
  ThisThread::sleep_for(50);
  block_for_epos_state(ReadyToSwitchOn);
}

void Epos4::startPosMode () {
  goToReadyState();

  // Set profile position mode (PPM)
  steering_can::put(constructCANMessage(epos4_messages::SetPPM_Data, NODE_ID));
  ThisThread::sleep_for(50);

  // TODO ? Setup PDOs

  // Switch on  (-> SwitchedOn), allow high voltage
  steering_can::put(epos4_messages::constructControlword(epos4_messages::SwitchOn, NODE_ID));
  ThisThread::sleep_for(50);
  block_for_epos_state(SwitchedOn);
  // Enable operation (-> OperationEnabled), allow torque
  steering_can::put(epos4_messages::constructControlword(epos4_messages::EnableOperation, NODE_ID));
  ThisThread::sleep_for(50);
  block_for_epos_state(OperationEnabled);
}

void Epos4::setHomePosition() {
  block_for_epos_state(OperationEnabled);
  steering_can::put(epos4_messages::constructHomePos(NODE_ID));
  ThisThread::sleep_for(50);
}

void Epos4::moveToAngle (float angle) {
  block_for_epos_state(OperationEnabled);

  pc.printf("Setting target position to : %f\n", angle);

  steering_can::put(epos4_messages::constructTargetPos(angle, NODE_ID));
  ThisThread::sleep_for(50);

  steering_can::put(epos4_messages::constructControlword(epos4_messages::ConfirmSetpoint, NODE_ID));
  ThisThread::sleep_for(50);
}

void Epos4::stop () {
  quickStop();

  epos_access.lock();
  epos_state state = epos_current_state;
  epos_access.unlock();

  if (state == QuickStopActive) {
    steering_can::put(epos4_messages::constructControlword(epos4_messages::DisableVoltage, NODE_ID));
    block_for_epos_state(SwitchOnDisabled);
  }
}

void Epos4::quickStop () {
  epos_access.lock();
  epos_state state = epos_current_state;
  epos_access.unlock();

  if (state == OperationEnabled) {
    steering_can::put(epos4_messages::constructControlword(epos4_messages::QuickStop, NODE_ID));
    block_for_epos_state(QuickStopActive);
  }
}

/* void resume() { */
/*   // Send <<EnableOperation>> */
/*   // Wait for OperationEnabled */
/* } */

/* void resetError() { */
/*   // Send <<Fault reset>> controlword */
/*   // Wait for SwitchOnDisabled */
/* } */

/* namespace EMCY { */
/*   getError( data ) { */
/*     // byte 0,1 = ErrorCode */
/*     // byte 2 = Error Register */
/*   } */

/*   resettableError ( errorCode ) { */
/*     // not resettables: */

/*     //  0x1080 ... 0x1083 - Generic Initialization error - reset device, if persist contact supplier */
/*     //  0x1090 - Firmware incompatibility error - reset / update firmware / contact supplier */
/*     //  0x3210 - Overvoltage error - Usually at deceleration (consult Firmware Specification for hardware solution, add capacitor), CAN TRY RESET - if voltage valid */
/*     //  0x4210 - Thermal overload error - CAN TRY RESET - if temperature in valid range */
/*     //  0x4380 - Thermal motor overload error - CAN TRY RESET if corrected */
/*     //  0x5113 - Logic voltage too low - CAN TRY RESET if corrected */

/*     //  0x5280 - reset device */
/*     //  0x5281 - reset device */
/*     //  0x5480 ... 0x5483 - reset device */
/*     //  0x6080,0x6081 - can reset + check extension 1 is connected, see manual */
/*     //  0x6380 - Set device parameters again */

/*     // 0x8120,0x8130 - send NMT reset communication */

/*     // 0x8181 - reset device */
/*   } */
/* } */

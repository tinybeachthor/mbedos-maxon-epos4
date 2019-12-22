#pragma once

#include "mbed.h"

namespace steering_can
{
  extern void init (PinName rx, PinName tx, uint32_t baudrate);

  extern bool get (CANMessage& msg, uint32_t timeout);
  extern bool put (const CANMessage& msg);
}

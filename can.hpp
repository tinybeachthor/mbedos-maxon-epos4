#pragma once

#include "mbed.h"

namespace can
{
  void init (PinName rx, PinName tx, const uint32_t baudrate = 500000);

  bool get (CANMessage& msg, uint32_t millisec = osWaitForever);
  bool put (const CANMessage& msg);
}

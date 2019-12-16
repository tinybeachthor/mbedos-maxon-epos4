#pragma once

#include "mbed.h"

static Serial pc(SERIAL_TX, SERIAL_RX);

static DigitalOut led_status(LED2);
static DigitalOut led_error(LED3);

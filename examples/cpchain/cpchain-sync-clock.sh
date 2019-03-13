#!/usr/bin/env bash

# synchronize system clock when connect to bootnode always fail
sudo apt-get install ntpdate

sudo ntpdate cn.pool.ntp.org

sudo hwclock --systohc
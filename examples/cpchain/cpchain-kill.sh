#!/usr/bin/env bash

ps -ef|grep cpchain|grep $1.log|awk '{print $2}'|xargs kill -9
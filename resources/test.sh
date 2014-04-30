#!/bin/sh
MathematicaScript -script test.m
notify-send "$(cat test_result.txt)"


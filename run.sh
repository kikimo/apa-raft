#!/bin/bash

apalache-mc check \
        --no-deadlock \
        --inv=Inv \
        MC.tla $@

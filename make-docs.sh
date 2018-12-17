#!/bin/bash

cargo doc
cp -r target/doc/* ./docs/

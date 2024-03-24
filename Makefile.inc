BACKEND ?= docker

ifeq ($(BACKEND),docker)
INTERACTIVE_OR_SEP := "-it"
CONTROLLER_NODE := "controller"
else
BACKEND := lxc
INTERACTIVE_OR_SEP := "--"
CONTROLLER_NODE := "sandtable-lxc"
endif

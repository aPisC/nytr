FROM ubuntu:kinetic
#FROM mcr.microsoft.com/vscode/devcontainers/base:ubuntu-20.04

RUN apt update
RUN apt install -y --no-install-recommends agda
#RUN apt install -y agda-mode


CMD exec /bin/bash -c "trap : TERM INT; sleep infinity & wait"

# Docker container spec for building the cpchain blockchain explorer
#
# VERSION               0.0.1

FROM ubuntu:16.04
LABEL maintainer="chengx@cpchain.io"

# set location
ENV TZ 'Asia/Shanghai'
RUN echo $TZ > /etc/timezone

RUN apt-get update; apt-get -y upgrade; apt-get -y install locales tzdata

WORKDIR /
RUN apt-get install -y git
RUN git clone https://github.com/Alex-Cheng/explorer
RUN apt-get install -y nodejs
RUN apt-get install -y npm

# A workaround for a bug, want: nodejs -> node
RUN ln -s /usr/bin/nodejs /usr/bin/node

RUN npm config set registry https://registry.npm.taobao.org
RUN npm install -g bower
WORKDIR /explorer
RUN npm install
RUN bower install --allow-root

CMD  /bin/sh -c "cd /explorer && npm start"

EXPOSE 8000

# run `
#   docker tag <image id> cpchain_blockchain_explorer:latest
# ` to tag the docker image.

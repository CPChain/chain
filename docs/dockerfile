FROM ubuntu:20.04 as builder

RUN apt-get update -y && apt-get install -y curl && curl -sL https://deb.nodesource.com/setup_16.x |  bash 

RUN apt-get update -y && apt-get -y install nodejs 

RUN npm install -g yarn 

COPY . /usr/src/docs-new

WORKDIR /usr/src/docs-new

RUN yarn install 

RUN yarn run docs:build

FROM nginx:1.19.7-alpine

COPY --from=0 /usr/src/docs-new/docs/.vuepress/dist /usr/share/nginx/html
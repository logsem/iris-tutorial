REGISTRY := ghcr.io/logsem/iris-tutorial
BASE_IMAGE := ocaml/opam:debian-12-ocaml-5.4

default:
	@echo 'Usage: make [x86-64 | arm64 | push-x86-64 | push-arm64]'

x86-64:
	docker build \
		--platform linux/amd64 \
		--build-context repo=.. \
		--build-arg BASE_IMAGE=$(BASE_IMAGE) \
		-t $(REGISTRY)/docker-x86-64 .

arm64:
	docker build \
		--platform linux/arm64 \
		--build-context repo=.. \
		--build-arg BASE_IMAGE=$(BASE_IMAGE) \
		-t $(REGISTRY)/docker-arm64 .

push-x86-64: x86-64
	docker push $(REGISTRY)/docker-x86-64

push-arm64: arm64
	docker push $(REGISTRY)/docker-arm64

.PHONY: x86-64 arm64 push-x86-64 push-arm64 default

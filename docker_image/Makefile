REGISTRY := ghcr.io/logsem/iris-tutorial
OCAML_VER := 5.5
MODE ?= stable

# Logic for Base Image and Tags
ifeq ($(MODE),unstable)
    BASE_IMAGE := ocaml/opam:debian-unstable-ocaml-5.5
    IMAGE_NAME := debian-unstable-ocaml-$(OCAML_VER)
else
    BASE_IMAGE := ocaml/opam:debian-ocaml-5.5
    IMAGE_NAME := debian-ocaml-$(OCAML_VER)
endif

default:
	@echo 'Usage: make [stable-x86-64 | unstable-x86-64 | stable-arm64 | unstable-arm64]'

# Internal build logic
build-%:
	$(eval ARCH_RAW := $*)
	$(eval PLATFORM := $(if $(filter x86-64,$(ARCH_RAW)),linux/amd64,linux/arm64))
	$(eval OPAM_ARCH := $(if $(filter x86-64,$(ARCH_RAW)),x86_64-linux,arm64-linux))

	# We use -f to point to the Dockerfile because the context is now ".."
	docker build \
		--platform $(PLATFORM) \
		--build-arg BASE_IMAGE=$(BASE_IMAGE) \
		--build-arg MODE=$(MODE) \
		-f Dockerfile \
		-t $(REGISTRY)/$(IMAGE_NAME)-$(ARCH_RAW) \
		..

# Public targets
stable-x86-64:
	$(MAKE) build-x86-64 MODE=stable

unstable-x86-64:
	$(MAKE) build-x86-64 MODE=unstable

stable-arm64:
	$(MAKE) build-arm64 MODE=stable

unstable-arm64:
	$(MAKE) build-arm64 MODE=unstable

# Push targets
push-stable-x86-64: stable-x86-64
	docker push $(REGISTRY)/debian-ocaml-$(OCAML_VER)-x86-64

push-unstable-x86-64: unstable-x86-64
	docker push $(REGISTRY)/debian-unstable-ocaml-$(OCAML_VER)-x86-64

push-stable-arm64: stable-arm64
	docker push $(REGISTRY)/debian-ocaml-$(OCAML_VER)-arm64

push-unstable-arm64: unstable-arm64
	docker push $(REGISTRY)/debian-unstable-ocaml-$(OCAML_VER)-arm64

.PHONY: stable-x86-64 unstable-x86-64 stable-arm64 unstable-arm64 \
	push-stable-x86-64 push-unstable-x86-64 push-stable-arm64 push-unstable-arm64 \
	default

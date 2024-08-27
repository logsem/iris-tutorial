default:
	@echo 'Please use one of the following targets: x86-64, push-x86-64, arm64, or push-arm64.'

x86-64:
	docker build --platform linux/amd64 -t ghcr.io/logsem/iris-tutorial/docker-x86-64 .

arm64:
	docker build --platform linux/arm64 -t ghcr.io/logsem/iris-tutorial/docker-arm64 .

push-x86-64: x86-64
	docker push ghcr.io/logsem/iris-tutorial/docker-x86-64

push-arm64: arm64
	docker push ghcr.io/logsem/iris-tutorial/docker-arm64

.phony: x86-64 push-x86-64 arm64 push-arm64 default
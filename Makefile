COMPILER=gcc
# -lm is required for math.h
FLAGS=-std=c99 -g -lm -Wall -Wextra -fsanitize=address -fno-omit-frame-pointer -Walloc-zero -Wcast-qual -Wconversion -Wformat=2 -O2

spesh:
	@mkdir -p build
	@$(COMPILER) ./examples/repl.c -o ./build/spesh $(FLAGS)
test: spesh
	@chmod +x ./scripts/test.sh
	@./scripts/test.sh build/spesh
clean:
	@rm -rf ./build


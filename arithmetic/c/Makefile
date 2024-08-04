# Compiler and flags
CC := ccomp
CFLAGS := -O -Xpreprocessor -Wno-cpp
AR := ar
ARFLAGS := rcs

# Directories
SRC_DIR := src
TARGET_DIR := target/$(SYSTEM)
OBJ_DIR := $(TARGET_DIR)
LIB_DIR := $(TARGET_DIR)


# Source files
SRCS := $(wildcard $(SRC_DIR)/*.c)

# Object files
OBJS := $(patsubst $(SRC_DIR)/%.c,$(OBJ_DIR)/%.o,$(SRCS))

# Target
LIB := $(LIB_DIR)/libarithmetic.a

# Main target
all: $(TARGET_DIR) $(LIB)

$(TARGET_DIR):
	mkdir -p $(TARGET_DIR)

# Rule to compile .c files into .o files
$(OBJ_DIR)/%.o: $(SRC_DIR)/%.c
	$(CC) $(CFLAGS) -c $< -o $@

# Rule to create static library
$(LIB): $(OBJS)
	$(AR) $(ARFLAGS) $@ $^

# Phony target to clean up generated files
.PHONY: clean
clean:
	rm -f $(OBJS) $(LIB)

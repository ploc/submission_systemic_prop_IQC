SRC = $(wildcard *.c)

# Separate the files into different categories
TWO_MASS_FILES = two_mass_model_verification.c two_mass_systemic_properties.c
OTHER_FILES = $(filter-out $(TWO_MASS_FILES), $(SRC))

all: $(TWO_MASS_FILES:%.c=%.run) $(OTHER_FILES:%.c=%.run)

# Define the rules for each category
# Rule for the two_mass files
$(TWO_MASS_FILES:%.c=%.run): %.run: %.c
	frama-c -wp -wp-model real -wp-cache none -wp-timeout 120 -wp-prover z3,alt-ergo,Alt-Ergo-Poly $<

# Rule for the other files
$(OTHER_FILES:%.c=%.run): %.run: %.c
	frama-c -wp -wp-model real -wp-cache none -wp-timeout 600 -wp-prover Alt-Ergo-Poly $<


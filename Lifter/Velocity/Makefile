.PHONY: all

VELC := velocity

THYS := Auto_Lifter.thy \
	Auto_Lifter_Sets.thy \
	Schem_Lift_Defs.thy

VELS := ${THYS:.thy=.velocity}

all: ${THYS}

%.thy: %.velocity
	${VELC} -t $< -o $@

clean:
	rm -f ${THYS}

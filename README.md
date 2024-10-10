# verify-systemic-properties

## Dependencies

### Alt-Ergo with OSDP plugin
- CSDP (https://github.com/coin-or/Csdp)
- OSDP: available through opam
  - opam install osdp
- Alt-Ergo
  - install from source using the following pull-request
  - https://github.com/OCamlPro/alt-ergo/pull/499
  
  
### Frama-C v. 25.0 (Manganese) (shall work with earlier version)
  - WP plugin (installed by default)
  - https://frama-c.com/html/get-frama-c.html
  - available through opam: opam install frama-c

## Configuration

You need to declare Alt-Ergo-Poly as a prover for Why3

First run 
```
why3 config detect
```
Edit ~/.why3.conf and add:

```
[prover]
command = "alt-ergo  --polynomial-plugin osdp-plugin.cmxs --timelimit %t %f"
driver = "alt_ergo"
name = "Alt-Ergo-Poly"
version = ""
```
## Use

Run

```
make
```

It will run the following analyses:

```
frama-c -wp -wp-timeout 600 -wp-cache none -wp-model real -wp-prover Alt-Ergo-Poly AUV_controller.c
[kernel] Parsing AUV_controller.c (with preprocessing)
[kernel:parser:decimal-float] AUV_controller.c:144: Warning: 
  Floating-point constant 0.01119 is not represented exactly. Will use 0x1.6eac8605681edp-7.
  (warn-once: no further messages from category 'parser:decimal-float' will be emitted)
[wp] Warning: Missing RTE guards
[wp] 20 goals scheduled
[wp] Proved goals:   20 / 20
  Qed:              16  (13ms-53ms-273ms)
  Alt-Ergo-Poly :    4  (2'6s-3'5s) (27558)

frama-c -wp -wp-timeout 600 -wp-cache none -wp-model real -wp-prover Alt-Ergo-Poly Hovercraft_Controller.c
[kernel] Parsing Hovercraft_Controller.c (with preprocessing)
[kernel:parser:decimal-float] Hovercraft_Controller.c:161: Warning: 
  Floating-point constant 0.21218 is not represented exactly. Will use 0x1.b28b6d86ec17fp-3.
  (warn-once: no further messages from category 'parser:decimal-float' will be emitted)
[wp] Warning: Missing RTE guards
[wp] 11 goals scheduled
[wp] Proved goals:   11 / 11
  Qed:               9  (7ms-16ms-54ms)
  Alt-Ergo-Poly :    2  (18.1s-21.4s) (4871)

frama-c -wp -wp-timeout 600 -wp-cache none -wp-model real -wp-prover Alt-Ergo-Poly UAS_controller.c
[kernel] Parsing UAS_controller.c (with preprocessing)
[kernel:parser:decimal-float] UAS_controller.c:140: Warning: 
  Floating-point constant 0.01907 is not represented exactly. Will use 0x1.387160956c0d7p-6.
  (warn-once: no further messages from category 'parser:decimal-float' will be emitted)
[wp] Warning: Missing RTE guards
[wp] 24 goals scheduled
[wp] Proved goals:   24 / 24
  Qed:              20  (10ms-48ms-346ms)
  Alt-Ergo-Poly :    4  (17.8s-1'5s) (15667)
  
```

Note that the floating point errors have been computed separately.

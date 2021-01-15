.. _fpu:

Floating Point Unit (FPU)
=========================

The RV32F ISA extension for floating-point support in the form of IEEE-754 single
precision can be enabled by setting the parameter **FPU** of the toplevel file
``cv32e40x_core.sv`` to 1. This will extend the |corev| decoder accordingly.
The FPU repository used by the |corev| core is available at
https://github.com/pulp-platform/fpnew.
In the core repository, a wrapper showing how the FPU is connected
to the core is available at ``example_tb/core/cv32e40x_fp_wrapper.sv``.
A dedicated register file consisting of 32
floating-point registers, ``f0``-``f31``, is instantiated.

The latency of the individual instructions are set by means of parameters in the
FPU repository (see https://github.com/pulp-platform/fpnew/tree/develop/docs).


FP CSR
------

When using floating-point extensions the standard specifies a
floating-point status and control register (:ref:`csr-fcsr`) which contains the
exceptions that occurred since it was last reset and the rounding mode.
:ref:`csr-fflags` and :ref:`csr-frm` can be accessed directly or via :ref:`csr-fcsr` which is mapped to
those two registers.

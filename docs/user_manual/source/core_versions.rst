Core Versions and RTL Freeze Rules
==================================

The |corev| is defined by the ``marchid`` and ``mimpid`` tuple.
The tuple identify which sets of parameters have been verified
by OpenHW Group, and once RTL Freeze is achieved, no further
non-logically equivalent changes are allowed on that set of parameters.

The RTL Freeze version of the core is indentified by a GitHub
tag with the format |corev_lc|\ _vMAJOR.MINOR.PATCH (e.g. |corev_lc|\ _v1.0.0).
In addition, the release date is reported in the documentation.

What happens after RTL Freeze?
------------------------------

A bug is found
^^^^^^^^^^^^^^

If a bug is found that affect the already frozen parameter set,
the RTL changes required to fix such bug are non-logically equivalent by definition.
Therefore, the RTL changes are applied only on a different  ``mimpid``
value and the bug and the fix must be documented.
These changes are visible by software as the ``mimpid`` has a different value.
Every bug or set of bugs found must be followed by another RTL Freeze release and a new GitHub tag.

RTL changes on non-verified yet parameters
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

If changes affecting the core on a non-frozen parameter set are required, then
such changes must remain logically equivalent for the already frozen set of parameters (except for the required mimpid update), and they must be applied on a different ``mimpid`` value. They can be non-logically equivalent to a non-frozen set of parameters.
These changes are visible by software as the ``mimpid`` has a different value.
Once the new set of parameters is verified and achieved the sign-off for RTL freeze,
a new GitHub tag and version of the core is released.

PPA optimizations and new features
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Non-logically equivalent PPA optimizations and new features are not allowed on a given set
of RTL frozen parameters (e.g., a faster divider).
If PPA optimizations are logically-equivalent instead, they can be applied without
changing the ``mimpid`` value (as such changes are not visible in software).
However, a new GitHub tag should be released and changes documented.

Released core versions
----------------------

The verified parameter sets of the core, their implementation version, GitHub tags,
and dates are reported here.


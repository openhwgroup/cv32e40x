.. _custom-isa-extensions:

CORE-V Instruction Set Extensions
=================================

Custom instructions
-------------------

|corev| supports the custom instruction(s) listed in :numref:`Custom instructions`.

.. table:: Custom instructions
  :name: Custom instructions
  :widths: 10 10 80
  :class: no-scrollbar-table

  +-------------------------+-------------+--------------------------------------------------+
  | Custom instruction      | Encoding    | Description                                      |
  +=========================+=============+==================================================+
  | ``wfe``                 | 0x8C00_0073 | Wait For Event, see :ref:`wfe`.                  |
  +-------------------------+-------------+--------------------------------------------------+

Further custom instructions can be added external to the core via the eXtension interface described in :ref:`x_ext`.

Custom CSRs
-----------

|corev| does not contain custom CSRs.

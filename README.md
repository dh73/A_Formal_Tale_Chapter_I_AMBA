# A Formal Tale, Chapter I: AMBA

Beware: This repository is still in beta version

---

## Table of contents

   * [A Formal Tale, Chapter I: AMBA](#a-formal-tale-chapter-i-amba)
      * [Table of contents](#table-of-contents)
      * [AMBA Formal Properties Repository](#amba-formal-properties-repository)
         * [AXI4-Stream](#axi4-stream)
            * [AXI4-Stream Examples](#axi4-stream-examples)
         * [AXI4 Lite/Full](#axi4-litefull)
            * [AXI4 Lite/Full Propositions](#axi4-litefull-propositions)
            * [AXI4 Lite/Full Examples](#axi4-litefull-examples)
      * [Motivation](#motivation)
         * [Good organisation of the code](#good-organisation-of-the-code)
         * [Debuggability](#debuggability)
         * [Documentation](#documentation)
         * [Optimised properties for model checking.](#optimised-properties-for-model-checking)
         * [Be used as reference for others to see the power of SVA](#be-used-as-reference-for-others-to-see-the-power-of-sva)


---


## AMBA Formal Properties Repository
### AXI4-Stream
* [AXI4 Stream](https://github.com/dh73/A_Formal_Tale_Chapter_I_AMBA/tree/main/AXI/AXI4_STREAM)
#### AXI4-Stream Examples
* [Example 01: Source to sink (self check)](https://github.com/dh73/A_Formal_Tale_Chapter_I_AMBA/tree/main/AXI/AXI4_STREAM/examples/dd01_self_check)
* [Example 02: Verify another VIP (faxis_slave)](https://github.com/dh73/A_Formal_Tale_Chapter_I_AMBA/tree/main/AXI/AXI4_STREAM/examples/dd02_compare)
* [Example 03: AXI4-Stream FIFO from Alex Forencich's](https://github.com/dh73/A_Formal_Tale_Chapter_I_AMBA/tree/main/AXI/AXI4_STREAM/examples/dd03_axis_fifo)
* [Example 04: AXI4-Stream Mat - mul from rahulsridhar5/PLCgroup10](https://github.com/dh73/A_Formal_Tale_Chapter_I_AMBA/tree/main/AXI/AXI4_STREAM/examples/dd04_mat_mul)
### AXI4 Lite/Full
* [AXI4 Lite/Full](https://github.com/dh73/A_Formal_Tale_Chapter_I_AMBA/tree/main/AXI/AXI4_LITE_FULL)
#### AXI4 Lite/Full Propositions
* [AXI4 Lite/Full Propositions](https://github.com/dh73/A_Formal_Tale_Chapter_I_AMBA/blob/main/AXI/AXI4_LITE_FULL/AXI4%20Lite_Full%20Propositions.xlsx)
#### AXI4 Lite/Full Examples
* [Example 01: Spinal HDL Component (lite)](https://github.com/dh73/A_Formal_Tale_Chapter_I_AMBA/tree/main/AXI/AXI4_LITE_FULL/examples/spinal_axi4_lite)

---

## Motivation

The goal of this repository of AMBA properties for Formal Verification is to showcase how to get the most of both AMBA and Model Checking in design and verification of AMBA AXI IP in conjunction with these pillars:

- Good organisation of the code.
- Debuggability.
- Documentation.
- Optimised properties for model checking.
- Be a reference for others to see the power of SVA, and that strong properties are not necessarily complex.

The following sections briefly describe these points.

* * *

### Good organisation of the code

This implementation uses the SVA `property` ... `endproperty` constructs to define the rules that are to be proven, and a link to the specification where said behavior is mentioned, as shown in the excerpt below:

```verilog
   /*            ><><><><><><><><><><><><><><><><><><><><             *
    *            Section III: Handshake Rules.                        *
    *            ><><><><><><><><><><><><><><><><><><><><             */
   /* ,         ,                                                     * 
    * |\\\\ ////| "Once TVALID is asserted it must remain asserted    * 
    * | \\\V/// |  until the handshake (TVALID) occurs".              * 
    * |  |~~~|  | Ref: 2.2.1. Handshake Protocol, p2-3.               * 
    * |  |===|  |                                                     * 
    * |  |A  |  |                                                     * 
    * |  | X |  |                                                     * 
    *  \ |  I| /                                                      * 
    *   \|===|/                                                       * 
    *    '---'                                                        */
   property tvalid_tready_handshake;
      @(posedge ACLK) disable iff (!ARESETn)
        TVALID && !TREADY |-> ##1 TVALID;
   endproperty // tvalid_tready_handshake
```

This increases readability and encapsulates common behaviors easily, so debugging can be less difficult.

* * *

### Debuggability

A message accompanies the assertion in the action block, so when a failure is found by the new VIP, the user can quickly understand the root cause and fix the problem faster.

```verilog
assert_SRC_TVALID_until_TREADY: assert property (tvalid_tready_handshake)
           else $error ("Protocol Violation: Once TVALID is asserted \ 
           it must remain asserted until the handshake occurs (2.2.1, p2-3).");
```

* * *

### Documentation

There will be an user guide and a set of examples so the user can start real quick to get RoI of using formal for both RTL design bring-up and verification tasks. See, for example, this demonstration using the new VIP.

* * *

### Optimised properties for model checking.

The aim is to reduce the size of the new verification IP in terms of variables, so it can be used in large designs. To achieve this, the properties should have only the required variables in the antecedent, and complex behaviors will use auxiliary logic instead of, for example, sequences or any other SVA structure that is not formal friendly.

* * *

### Be used as reference for others to see the power of SVA
By correlating the specification with the property block, users can understand why the property was encoded in that way.

Upon failures, the user would be able to quickly understand the issues, since this repository is open source and does not follow the industrial solution where the IP uses antecedent and consequent of the propositions encrypted, adding unnecessary complexity to the debug.
# A Formal Tale, Chapter I: AMBA

Beware: This repository is still in beta version

---

## The beginning

<details><summary>A little (and bad) story that you can read if you have free time.</summary>

There was once a company that developed an open-standard for on-chip interconnect specification and management of functional blocks in a thing called SoC (System On Chip). They named it AMBA (for Advanced Microcontroller Bus Architecture), and although its name suggests that it was created for microcontrollers, thanks to the urgency of some people to create increasingly complex systems to be able to send more and more rare images which they call memes, to strangers, this standard became very popular in a short time.

Given the complexity of the systems where the AMBA bus was used, the standard was forced to evolve to better adapt to the requirements of high frequency, high performance, and so on. An improved standard emerged and was named AXI.

The complexity that grew over time in the implementations that used the AMBA AXI standard attracted the attention of some strange beings that people called "bugs". These bugs loved to hide in the implementation, in all kinds of places: from spots where they could be observed with obviousness, to locations where probably no one has found them yet.

These bugs are in charge of preventing the implementations from doing their job, because it sounds like fun. But in reality it is not, because people lose sleep, suffer, stop eating, looking for these playful bugs to be able to remove them so that they stop interfering with the functionality of the designs.

But all was not lost, some magicians wrote magic recipes that they called VIP (Verification IP). They used strange oracles together with those recipes, to track down all these bugs in a fraction of seconds, and thus return happiness to people, but that in exchange for hectares of land, one hundred goats and twenty cows. No one refused, since they were the only ones who could do that.

A blue-and-green giant lizard emerged to support people who had neither land, nor goats nor cows, and forged with his hands artifacts similar to those used by the magicians, to find the dangerous bugs. Then gave it to the people and trusted that they would do the rest.

Some of them did, some others not so much, but meanwhile AXI implementations keep attracting more and more bugs over the time. This giant lizard got worried and started working on this. And here it is, the beginning of the adventure. Could it be successful? What difficulties will there be? ...

*This story is terrible, but not as terrible as the ones you could tell me if you don't use formal verification in your designs*.

</details>


* * *

## Table of contents
   * [A Formal Tale, Chapter I: AMBA](#a-formal-tale-chapter-i-amba)
      * [The beginning](#the-beginning)
      * [Table of contents](#table-of-contents)
      * [New SEDA AMBA Formal VIP](#new-seda-amba-formal-vip)
         * [AXI4-Stream VIP](#axi4-stream-vip)
            * [AXI4-Stream VIP Examples](#axi4-stream-vip-examples)
         * [AXI4 Lite/Full VIP](#axi4-litefull-vip)
            * [AXI4 Lite/Full VIP Propositions](#axi4-litefull-vip-propositions)
            * [AXI4 Lite/Full VIP Examples](#axi4-litefull-vip-examples)
      * [Motivation](#motivation)
         * [Develop a new IP that fixes important issues that exists in the current implementation with the solely purpose of enhance the Symbiotic EDA Suite VIP catalog](#develop-a-new-ip-that-fixes-important-issues-that-exists-in-the-current-implementation-with-the-solely-purpose-of-enhance-the-symbiotic-eda-suite-vip-catalog)
            * [Issues in AXI4 Lite Sink](#issues-in-axi4-lite-sink)
            * [Issues in AXI4 Lite Source](#issues-in-axi4-lite-source)
            * [Issues in AXI4 Full Source](#issues-in-axi4-full-source)
               * [Unreachable constraints](#unreachable-constraints)
               * [Vacuous properties](#vacuous-properties)
                  * [Vacuity proof](#vacuity-proof)
            * [Issues in the AXI4 Stream Sink](#issues-in-the-axi4-stream-sink)
         * [Better organisation of the code](#better-organisation-of-the-code)
         * [Improve debuggability](#improve-debuggability)
         * [Improve documentation](#improve-documentation)
         * [Optimise the properties for model checking.](#optimise-the-properties-for-model-checking)
         * [Be used as reference for others to see the power of SVA](#be-used-as-reference-for-others-to-see-the-power-of-sva)

---


## New SEDA AMBA Formal VIP
### AXI4-Stream VIP
* [AXI4 Stream](https://github.com/dh73/A_Formal_Tale_Chapter_I_AMBA/tree/main/AXI/AXI4_STREAM)
#### AXI4-Stream VIP Examples
* [Example 01: Source to sink (self check)](https://github.com/dh73/A_Formal_Tale_Chapter_I_AMBA/tree/main/AXI/AXI4_STREAM/examples/dd01_self_check)
* [Example 02: Verify another VIP (faxis_slave)](https://github.com/dh73/A_Formal_Tale_Chapter_I_AMBA/tree/main/AXI/AXI4_STREAM/examples/dd02_compare)
* [Example 03: AXI4-Stream FIFO from Alex Forencich's](https://github.com/dh73/A_Formal_Tale_Chapter_I_AMBA/tree/main/AXI/AXI4_STREAM/examples/dd03_axis_fifo)
* [Example 04: AXI4-Stream Mat - mul from rahulsridhar5/PLCgroup10](https://github.com/dh73/A_Formal_Tale_Chapter_I_AMBA/tree/main/AXI/AXI4_STREAM/examples/dd04_mat_mul)
### AXI4 Lite/Full VIP
* [AXI4 Lite/Full](https://github.com/dh73/A_Formal_Tale_Chapter_I_AMBA/tree/main/AXI/AXI4_LITE_FULL)
#### AXI4 Lite/Full VIP Propositions
	* [AXI4 Lite/Full Propositions](https://github.com/dh73/A_Formal_Tale_Chapter_I_AMBA/blob/main/AXI/AXI4_LITE_FULL/AXI4%20Lite_Full%20Propositions.xlsx)
#### AXI4 Lite/Full VIP Examples
	* [Example 01: Spinal HDL Component (lite)](https://github.com/dh73/A_Formal_Tale_Chapter_I_AMBA/tree/main/AXI/AXI4_LITE_FULL/examples/spinal_axi4_lite)

---

## Motivation

This new AMBA VIP aims to improve the quality of the current AXI verification components that are distributed as part of Symbiotic EDA Suite, by working on these areas:

- Develop a new IP that fixes important issues that exists in the current implementation with the solely purpose of enhance the Symbiotic EDA Suite VIP catalog.
- Better organisation of the code.
- Improve debuggability.
- Improve documentation.
- Optimise the properties for model checking.
- Be a reference for others to see the power of SVA, and that strong properties are not necessarily complex.

The following sections briefly describe these points.

* * *

### Develop a new IP that fixes important issues that exists in the current implementation with the solely purpose of enhance the Symbiotic EDA Suite VIP catalog

- Brief description: The AXI VIP under `20200902A/examples/formal-vip` is good to find bugs, but not to prove the absence of them (the VIP itself has some inconsistencies). It is also incomplete because it does not implement all the rules of the AMBA AXI protocol.

The current implementation suffers from some important problems that needs to be fixed. Below are some of those problems found during a quick review\[1\]:

\[1\] These *issues* were found in the licensed components distributed by SEDA Suite, specifically in the version 20200902A, under `examples/formal-vip` directory.

#### Issues in AXI4 Lite Sink

- Test details:
- **Directory of the VIP**: `20200902A/examples/formal-vip/axi-lite`
- **Which design**: `demoaxi (demoaxi.sby)`

The `Xilinx's extensions` in the `faxil_slave.v` suffer from unreachability in one of the constraints.  
In the excerpt below from `faxil_slave.v` (lines 478 to 482), the precondition of the `assumption` that restricts `i_axi_wvalid` *is unreachable*.

```verilog
        always @(posedge i_clk)
        if ((i_axi_reset_n)
                &&(f_axi_awr_outstanding > 1)
                &&(f_axi_awr_outstanding-1 > f_axi_wr_outstanding))
            `SLAVE_ASSUME(i_axi_wvalid);
```

Why is this important?, because an unreachable constraint create false confidence of behaviors correctly observed in the logic (if such behaviors are influenced by the constraint). But in reality, *a conflict can make some properties to never trigger*, in other words, properties pass because never failed but because they were never tested (vacuity). Is important to solve any vacuity that might be present.

To prove that this is an unreachable constraint, this cover statement can be used to check the reachability of the antecedent (this is nothing but the same precondition of the assumption, but used in a cover statement instead):

```verilog
always @(posedge i_clk)
                cover ((i_axi_reset_n) && (f_axi_awr_outstanding > 1) && (f_axi_awr_outstanding-1 > f_axi_wr_outstanding));
```

This cover is inserted around lines 484 and 485 in the `faxil_slave.v` file. Executing SBY in `cover` mode, gives the following result proving that there is a problem  (`Unreached cover statement at faxil_slave.v:485`):

```bash
[...]
SBY 21:30:27 [demoaxi_cvr] engine_0: ##   0:00:33  Checking cover reachability in step 35..
SBY 21:30:28 [demoaxi_cvr] engine_0: ##   0:00:35  Checking cover reachability in step 36..
SBY 21:30:30 [demoaxi_cvr] engine_0: ##   0:00:36  Checking cover reachability in step 37..
SBY 21:30:31 [demoaxi_cvr] engine_0: ##   0:00:38  Checking cover reachability in step 38..
SBY 21:30:33 [demoaxi_cvr] engine_0: ##   0:00:39  Checking cover reachability in step 39..
SBY 21:30:34 [demoaxi_cvr] engine_0: ##   0:00:41  Unreached cover statement at faxil_slave.v:485.
```

Following the same reasoning, these three properties pass vacuos as well:

```verilog
    // That means that requests need to stop when we're almost full
    always @(posedge i_clk)
    if (f_axi_awr_outstanding == { {(F_LGDEPTH-1){1'b1}}, 1'b0} )
        assert(!i_axi_awvalid);
    always @(posedge i_clk)
    if (f_axi_wr_outstanding == { {(F_LGDEPTH-1){1'b1}}, 1'b0} )
        assert(!i_axi_wvalid);
    always @(posedge i_clk)
    if (f_axi_rd_outstanding == { {(F_LGDEPTH-1){1'b1}}, 1'b0} )
        assert(!i_axi_arvalid);
```

To prove that statement, the curious reader would create a cover property to check that `f_axi_awr_outstanding`, `f_axi_wr_outstanding` and `f_axi_rd_outstanding` reaches the value of, in this case, `4'b1110` or `{(F_LGDEPTH-1){1'b1}}, 1'b0}`. A failure is expected since these cover scenarios are unreachable as well.

- For example, the reachability analysis for `f_axi_awr_outstanding` covering the precondition (inserted in line 547):

```verilog
always @(posedge i_clk) cover (f_axi_awr_outstanding == { {(F_LGDEPTH-1){1'b1}}, 1'b0} );
```

Results in :

```bash
0:00:38  Unreached cover statement at faxil_slave.v:547.
```

* * *

#### Issues in AXI4 Lite Source

This implementation has not been reviewed yet. But for practical purposes it can be assumed that, the same defects that show up in the sink, are found in the source too.

* * *

#### Issues in AXI4 Full Source

- Test details:
- **Directory of the VIP**: `20200902A/examples/formal-vip/axi`
- **Which design**: `axixbar (axixbar.sby)`

##### Unreachable constraints  
The following section shows the unreachable constraints found.

`faxi_master.v` line 768:

```verilog
`SLAVE_ASSERT((f_axi_rdid_ckign_nbursts != 1)
                ||(i_axi_rlast == (f_axi_rdid_ckign_outstanding==1)));
```

Proof:  
Inserted a cover statement as follows:

```verilog
 755  always @(*) cover (i_axi_rvalid && f_axi_rd_checkid == i_axi_rid && f_axi_rd_ckvalid && f_axi_rdid_ckign_nbursts > 0);
```

With the following result:

```bash
0:01:36  Unreached cover statement at faxi_master.v:755.
```

Following the same reasoning, unreachability can be proven in the following assumptions as well:

| **Location**    |  **Unreachable constraint**   |
| --- | --- |
| faxi_master.v:841 | `SLAVE\_ASSERT(next\_rdid\_nbursts >= next\_rdign_nbursts + 1); |
| faxi_master.v:842 | `SLAVE\_ASSERT(next\_rdid\_nbursts <= next\_rdid\_outstanding - next\_rdign\_outstanding - f\_axi\_rd\_cklen); |
| faxi_master.v:843 | `SLAVE\_ASSERT(next\_rdid\_outstanding >= next\_rdign\_outstanding + f\_axi\_rd\_cklen); |
| faxi_master.v:844 | `SLAVE\_ASSERT(next\_rdign\_nbursts <= next\_rdign_outstanding); |
| faxi_master.v:847 | `SLAVE\_ASSERT(next\_rdid\_nbursts >= ((i\_axi\_rvalid & i\_axi_rlast)?0:1)); |
| faxi_master.v:848 | `SLAVE\_ASSERT(next\_rdid\_outstanding >= (f\_axi\_rd\_cklen-1) + f\_axi\_rdid_nbursts - 1); |

And about 18 more that are not listed in the table.

##### Vacuous properties

An important amount of vacuous properties were found. For example, the following rule listed in `faxi_master.v`: 742 is vacuous:

```verilog
assert(f_axi_rdid_nbursts >= f_axi_rdid_ckign_nbursts+1);
```

###### Vacuity proof
It does not matter the variables that this property checks, it will pass all the time because it never triggers. For example, changing the property to this obviously wrong values:

```verilog
assert(f_axi_rdid_nbursts >= f_axi_rdid_ckign_nbursts+100);
```

Still passed:

```bash
SBY 14:09:03 [axixbar] engine_0.basecase: ##   0:00:49  Status: passed
[...]
SBY 14:15:46 [axixbar] engine_0: Status returned by engine for induction: pass
[...]
SBY 14:15:46 [axixbar] DONE (PASS, rc=0)
```

Following the same reasoning vacuity can be proven in the following assertions as well:

| **Location** | **Vacuous Proof** |
| --- | --- |
| faxi_master.v:744 | assert(f\_axi\_rdid_outstanding == f\_axi\_rdid\_ckign\_outstanding+f\_axi\_rd_cklen); |
| faxi_master.v:746 | assert(f\_axi\_rdid_outstanding >= f\_axi\_rdid\_ckign\_outstanding \+ f\_axi\_rd_cklen \+ (f\_axi\_rdid\_nbursts-(f\_axi\_rdid\_ckign_nbursts+1))); |
| faxi_master.v:1266 | assert((f\_axi\_rd_ckarlen == 15) \|(f\_axi\_rd_ckarlen == 7) \|(f\_axi\_rd_ckarlen == 3) \|(f\_axi\_rd_ckarlen == 1)); |

And about 9 more that are not listed in the table.

* * *

#### Issues in the AXI4 Stream Sink

- Test details:
- **Directory of the VIP**: `20200902A/examples/formal-vip/axi-lite`
- **Which design**: `$THIS_REPO/AXI/AXI4_STREAM/examples/dd02_compare/`

Some of the issues that affects the current `AXI4-Stream` implementation in `faxis_slave.v` are:

- Missing checks for optional TDATA.
- Weak implementation of the rules for reserved behaviors of TKEEP/TSTRB.
- Packet lost due incomplete implementation of the AMBA AXI4-Stream spec, regarding data and control information.

A document that describes these problems in more detail can be found [here](https://github.com/dh73/A_Formal_Tale_Chapter_I_AMBA/blob/main/AXI/AXI4_STREAM/examples/dd02_compare/dd02_compare.pdf).

* * *

### Better organisation of the code

The new implementation used the SVA `property` ... `endproperty` constructs to define the rules that are to be proven, and a link to the specification where said behavior is mentioned, as shown in the excerpt below:

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

### Improve debuggability

A message accompanies the assertion in the action block, so when a failure is found by the new VIP, the user can quickly understand the root cause and fix the problem faster.

```verilog
assert_SRC_TVALID_until_TREADY: assert property (tvalid_tready_handshake)
           else $error ("Protocol Violation: Once TVALID is asserted \ 
           it must remain asserted until the handshake occurs (2.2.1, p2-3).");
```

* * *

### Improve documentation

There will be an user guide and a set of examples so the user can start real quick to get RoI of using formal for both RTL design bring-up and verification tasks. See, for example, this demonstration using the new VIP.

* * *

### Optimise the properties for model checking.

The aim is to reduce the size of the new verification IP in terms of variables, so it can be used in large designs. To achieve this, the properties should have only the required variables in the antecedent, and complex behaviors will use auxiliary logic instead of, for example, sequences or any other SVA structure that is not formal friendly.

* * *

### Be used as reference for others to see the power of SVA

The new AXI4-Stream VIP implementation hopefully it is as clear as possible, and it can serve for other Symbiotic EDA suite users to add more behaviors that are not currently integrated in that VIP, so that they can have a greater value for their investment.

The development of the complete AXI4 (both lite and full) will follow the practices of the AXI4-Stream VIP.


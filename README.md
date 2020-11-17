# A Formal Tale, Chapter I: AMBA
Beware: This repository is still in beta version 

---

## The beginning
<details><summary>A little (and bad) story that you can read if you have free time.</summary>
<p>
There was once a company that developed an open-standard for on-chip interconnect specification and management of functional blocks in a thing called SoC (System On Chip). They named it AMBA (for Advanced Microcontroller Bus Architecture), and although its name suggests that it was created for microcontrollers, thanks to the urgency of some people to create increasingly complex systems to be able to send more and more rare images which they call memes, to strangers, this standard became very popular in a short time.

Given the complexity of the systems where the AMBA bus was used, the standard was forced to evolve to better adapt to the requirements of high frequency, high performance, and so on. An improved standard emerged and was named AXI. 

The complexity that grew over time in the implementations that used the AMBA AXI standard attracted the attention of some strange beings that people called "bugs". These bugs loved to hide in the implementation, in all kinds of places: from spots where they could be observed with obviousness, to locations where probably no one has found them yet.

These bugs are in charge of preventing the implementations from doing their job, because it sounds like fun. But in reality it is not, because people lose sleep, suffer, stop eating, looking for these playful bugs to be able to remove them so that they stop interfering with the functionality of the designs.

But all was not lost, some magicians wrote magic recipes that they called VIP (Verification IP). They used strange oracles together with those recipes, to track down all these bugs in a fraction of seconds, and thus return happiness to people, but that in exchange for hectares of land, one hundred goats and twenty cows. No one refused, since they were the only ones who could do that.

A blue-and-green giant lizard emerged to support people who had neither land, nor goats nor cows, and forged with his hands artifacts similar to those used by the magicians, to find the dangerous bugs. Then gave it to the people and trusted that they would do the rest.

Some of them did, some others not so much, but meanwhile AXI implementations keep attracting more and more bugs over the time. This giant lizard got worried and started working on this. And here it is, the beginning of the adventure. Could it be successful? What difficulties will there be? ...

_This story is terrible, but not as terrible as the ones you could tell me if you don't use formal verification in your designs_.

</p>
</details>

---


## Motivation
This new AMBA VIP aims to improve the quality of the current AXI verification components that are distributed as part of Symbiotic EDA Suite, by working on these areas:

* Develop a new IP that fixes important issues that exists in the current implementation with the solely purpose of enhance the Symbiotic EDA Suite VIP catalog.
* Better organisation of the code.
* Improve debuggability.
* Improve documentation.
* Optimise the properties for model checking.
* Be a reference for others to see the power of SVA, and that strong properties are not necessarily complex.

The following sections briefly describe these points.

---

### Develop a new IP that fixes important issues that exists in the current implementation with the solely purpose of enhance the Symbiotic EDA Suite VIP catalog
* Brief description: The AXI VIP under `20200902A/examples/formal-vip` is good to find bugs, but not to prove the absence of them (the VIP itself has some inconsistencies). It is also incomplete because it does not implement all the rules of the AMBA AXI protocol.

The current implementation suffers from some important problems that needs to be fixed. Below are some of those problems found during a quick review[1]:

[1] These _issues_ were found in the licensed components distributed by SEDA Suite, specifically in the version 20200902A, under `examples/formal-vip` directory. 

#### Issues in AXI Lite Sink:
* Test details:
* **Directory of the VIP**: `20200902A/examples/formal-vip/axi-lite`
* **Which design**: `demoaxi (demoaxi.sby`

The `Xilinx's extensions` in the `faxil_slave.v` suffer from unreachability in one of the constraints. 
In the excerpt below from `faxil_slave.v` (lines 478 to 482), the precondition of the `assumption` that restricts `i_axi_wvalid` *is unreachable*.

```verilog
		always @(posedge i_clk)
		if ((i_axi_reset_n)
				&&(f_axi_awr_outstanding > 1)
				&&(f_axi_awr_outstanding-1 > f_axi_wr_outstanding))
			`SLAVE_ASSUME(i_axi_wvalid);
```
Why is this important?, because an unreachable constraint create false confidence of behaviors correctly observed in the logic (if such behaviors are influenced by the constraint). But in reality, *a conflict can make some properties to never trigger*, in other words, properties pass because never failed but because they were never tested (vacuity). Is important to resolve any vacuity that might be present.

To prove that this is an unreachable constraint, this cover statement can be used to check the reachability of the antecedent (this is nothing but the same precondition of the assumption, but used in a cover statement instead):
```verilog
always @(posedge i_clk)
                cover ((i_axi_reset_n) && (f_axi_awr_outstanding > 1) && (f_axi_awr_outstanding-1 > f_axi_wr_outstanding));
```
This cover is inserted around lines 484 and 485 in the `faxil_slave.v` file. Executing SBY in `prove` mode, gives the following result, proving there is a problem `Unreached cover statement at faxil_slave.v:485.`: 

```bash
SBY 21:30:19 [demoaxi_cvr] engine_0: ##   0:00:26  Checking cover reachability in step 24..
SBY 21:30:19 [demoaxi_cvr] engine_0: ##   0:00:26  Checking cover reachability in step 25..
SBY 21:30:20 [demoaxi_cvr] engine_0: ##   0:00:26  Checking cover reachability in step 26..
SBY 21:30:20 [demoaxi_cvr] engine_0: ##   0:00:27  Checking cover reachability in step 27..
SBY 21:30:21 [demoaxi_cvr] engine_0: ##   0:00:28  Checking cover reachability in step 28..
SBY 21:30:22 [demoaxi_cvr] engine_0: ##   0:00:28  Checking cover reachability in step 29..
SBY 21:30:22 [demoaxi_cvr] engine_0: ##   0:00:29  Checking cover reachability in step 30..
SBY 21:30:23 [demoaxi_cvr] engine_0: ##   0:00:30  Checking cover reachability in step 31..
SBY 21:30:24 [demoaxi_cvr] engine_0: ##   0:00:31  Checking cover reachability in step 32..
SBY 21:30:25 [demoaxi_cvr] engine_0: ##   0:00:32  Checking cover reachability in step 33..
SBY 21:30:26 [demoaxi_cvr] engine_0: ##   0:00:33  Checking cover reachability in step 34..
SBY 21:30:27 [demoaxi_cvr] engine_0: ##   0:00:33  Checking cover reachability in step 35..
SBY 21:30:28 [demoaxi_cvr] engine_0: ##   0:00:35  Checking cover reachability in step 36..
SBY 21:30:30 [demoaxi_cvr] engine_0: ##   0:00:36  Checking cover reachability in step 37..
SBY 21:30:31 [demoaxi_cvr] engine_0: ##   0:00:38  Checking cover reachability in step 38..
SBY 21:30:33 [demoaxi_cvr] engine_0: ##   0:00:39  Checking cover reachability in step 39..
SBY 21:30:34 [demoaxi_cvr] engine_0: ##   0:00:41  Unreached cover statement at faxil_slave.v:485.
```

Under that same reasoning, these three properties pass vacuos as well:
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

To prove that statement, the curious reader would create a cover property to check that `f_axi_awr_outstanding`, `f_axi_wr_outstanding` and  `f_axi_rd_outstanding` reaches the value of, in this case, `4'b1110` or `{(F_LGDEPTH-1){1'b1}}, 1'b0}`. And, of course, these cover scenarios are unreachable as well.

* For example, the reachability analysis for `f_axi_awr_outstanding` covering the precondition (inserted in line 547):
```verilog
always @(posedge i_clk) cover (f_axi_awr_outstanding == { {(F_LGDEPTH-1){1'b1}}, 1'b0} );
```
Results in :
```bash
0:00:38  Unreached cover statement at faxil_slave.v:547.
```

---

#### Issues in AXI Lite Source:
This implementation has not been reviewed yet. But for practical purposes it can be assumed that, the same defects that show up in the sink, are found in the source too.

---

#### Issues in the AXI4-Stream Sink:
* Test details:
* **Directory of the VIP**: `20200902A/examples/formal-vip/axi-lite`
* **Which design**: `$THIS_REPO/AXI/AXI4_STREAM/examples/dd02_compare/`

Some of the issues that affects the current `AXI4-Stream` implementation in `faxis_slave.v` are:
* Missing checks for optional TDATA.
* Weak implementation of the rules for reserved behaviors of TKEEP/TSTRB.
* Packet lost due incomplete implementation of the AMBA AXI4-Stream spec, regarding data and control information.

A document that describes these problems in more detail can be found [here](https://github.com/dh73/A_Formal_Tale_Chapter_I_AMBA/blob/main/AXI/AXI4_STREAM/examples/dd02_compare/dd02_compare.pdf).

---


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

---

### Improve debuggability
A message accompanies the assertion in the action block, so when a failure is found by the new VIP, the user can quickly understand the root cause and fix the problem faster.

```verilog
assert_SRC_TVALID_until_TREADY: assert property (tvalid_tready_handshake)
           else $error ("Protocol Violation: Once TVALID is asserted \ 
		   it must remain asserted until the handshake occurs (2.2.1, p2-3).");
```

---

### Improve documentation
There will be an user guide and a set of examples so the user can start real quick to get RoI of using formal for both RTL design bring-up and verification tasks. See, for example, this demonstration using the new VIP.

---


### Optimise the properties for model checking.
The aim is to reduce the size of the new verification IP in terms of variables, so it can be used in large designs. To achieve this, the properties should have only the required variables in the antecedent, and complex behaviors will use auxiliary logic instead of, for example, sequences or any other SVA structure that is not formal friendly.

---

### Be used as reference for others to see the power of SVA
The new AXI4-Stream VIP implementation hopefully it is as clear as possible, and it can serve for other Symbiotic EDA suite users to add more behaviors that are not currently integrated in that VIP, so that they can have a greater value for their investment.

The development of the complete AXI4 (both lite and full) will follow the practices of the AXI4-Stream VIP.

---

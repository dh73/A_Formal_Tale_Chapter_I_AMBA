/*  AXI4 Formal Properties.
 *  Copyright (C) 2021  Diego Hernandez <diego@yosyshq.com>
 *                                      <dhdezr@fpgaparadox.com>
 *  Permission to use, copy, modify, and/or distribute this software for any
 *  purpose with or without fee is hereby granted, provided that the above
 *  copyright notice and this permission notice appear in all copies.
 *
 *  THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 *  WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 *  MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 *  ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 *  WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 *  ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 *  OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *
 */
`ifndef __AMBA_AXI4_SINGLE_INTERFACE_REQUIREMENTS__
 `define __AMBA_AXI4_SINGLE_INTERFACE_REQUIREMENTS__
package amba_axi4_single_interface_requirements;
   /*		 ><><><><><><><><><><><><><><><><><><><><             *
    *		 Section A3.1.2: Reset                                *
    *		 ><><><><><><><><><><><><><><><><><><><><	      */

   /* ,         ,                                                     *
    * |\\\\ ////|  "The earliest point after reset that a source is   *
    * | \\\V/// |   permitted to begin driving ARVALID, AWVALID, or   *
    * |	 |~~~|	|   WVALID HIGH is at a rising ACLK edge after        *
    * |	 |===|	|   ARESETn is HIGH".                                 *
    * |	 |A  |	|   Ref: A3.1.2 Reset, pA3-38, Figure A3-1.	      *
    * |	 | X |	|						      *
    *  \ |  I| /						      *
    *	\|===|/							      *
    *	 '---'							      */
   property exit_from_reset(aresetn, ep, valid);
      (!aresetn || ep) |-> !valid;
   endproperty // exit_from_reset

   /*		 ><><><><><><><><><><><><><><><><><><><><             *
    *		 Section A3.2.1: Handshake process                    *
    *		 ><><><><><><><><><><><><><><><><><><><><	      */

   /* ,         ,                                                     *
    * |\\\\ ////|  "The source presents the address, data or control  *
    * | \\\V/// |   information [...] and asserts the VALID signal.   *
    * |	 |~~~|  |   The destination asserts the READY signal [...]    *
    * |	 |===|  |   and the source must keep its information stable   *
    * |	 |A  |  |   until the transfer occurs".                       *
    * |	 | X |  |   Ref: A3.2.1 Handshake process, pA3-39,            *
    *  \ |  I| /    Figure A3-2                                       *
    *   \|===|/							      *
    *    '---'							      */
   property stable_before_handshake(valid, ready, control);
      valid && !ready |-> ##1 $stable(control);
   endproperty // stable_before_handshake

   /* ,         ,                                                     *
    * |\\\\ ////| "Once VALID is asserted it must remain asserted     *
    * | \\\V/// |  until the handshake occurs, at a rising clock edge *
    * |  |~~~|  |  at which VALID and READY are both asserted".	      *
    * |  |===|  |  Ref: A3.2.1 Handshake process, pA3-39. 	      *
    * |  |A  |  |						      *
    * |  | X |  |						      *
    *  \ |  I| /						      *
    *   \|===|/							      *
    *    '---'							      */
   property valid_before_handshake(valid, ready);
      valid && !ready |-> ##1 valid;
   endproperty // valid_before_handshake

   /* ,         ,                                                     *
    * |\\\\ ////|  "The source presents the address, data or control  *
    * | \\\V/// |   information [...] and asserts the VALID signal.   *
    * |	 |~~~|	|   The destination asserts the READY signal [...]    *
    * |	 |===|	|   until the transfer occurs [...], when this        *
    * |	 |A  |	|   assertion is recognized.                          *
    * |	 | X |	|   Ref: A3.2.1 Handshake process, pA3-39,            *
    *  \ |  I| /    Figure A3-2.                                      *
    *   \|===|/							      *
    *    '---'							      */
   property valid_before_ready(valid, ready);
      valid && !ready;
   endproperty // valid_before_ready

   /* ,         ,                                                     *
    * |\\\\ ////|   "The destination asserts READY [...] indicating   *
    * | \\\V/// |    that it can accept information. The source       *
    * |	 |~~~|	|    asserts VALID after [...] In this case, transfer *
    * |	 |===|	|    occurs in a single cycle".                       *
    * |	 |A  |	|    Ref: A3.2.1 Handshake process, pA3-39            *
    * |	 | X |	|    Figure A3-3.                                     *
    *  \ |  I| /                                                      *
    *   \|===|/							      *
    *    '---'							      */
   property ready_before_valid(valid, ready);
      ready && !valid;
   endproperty // ready_before_valid

   /* ,         ,                                                     *
    * |\\\\ ////|  "Both the source and destination happen to         *
    * | \\\V/// |   indicate [...] that they can transfer the payload *
    * |	 |~~~|  |   In this case the transfer occurs at the rising    *
    * |	 |===|	|   clock edge when the assertion of both VALID and   *
    * |	 |A  |	|   READY can be recognized".                         *
    * |	 | X |	|   Ref: A3.2.1 Handshake process, pA3-40,            *
    *  \ |  I| /    Figure A3-4.                                      *
    *   \|===|/	   		                                      *
    *    '---'							      */
   property valid_with_ready(valid, ready);
      valid && ready;
   endproperty // valid_with_ready

   // Deadlock (ARM Recommended)
   /* ,         ,                                                     *
    * |\\\\ ////|  It is recommended that READY is asserted within    *
    * | \\\V/// |  MAXWAITS cycles of VALID being asserted.	      *
    * |	 |~~~|	|  This is a *potential deadlock check* that can be   *
    * |	 |===|	|  implemented as well using the strong eventually    *
    * |	 |A  |	|  operator (if the required bound is too large to be *
    * |	 | X |	|  formally efficient). Otherwise this bounded        *
    *  \ |  I| /   property works fine.                               *
    *	\|===|/							      *
    *	 '---'							      */
   property handshake_max_wait(valid, ready, timeout);
      valid & !ready |-> ##[1:timeout] ready;
   endproperty // handshake_max_wait

   /*		 ><><><><><><><><><><><><><><><><><><><><             *
    *	      Section A3.2.2: Channel signaling requirements          *
    *		 ><><><><><><><><><><><><><><><><><><><><	      */
endpackage // amba_axi4_single_interface_requirements
`endif

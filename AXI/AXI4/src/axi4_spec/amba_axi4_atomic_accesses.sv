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
`ifndef __AMBA_AXI4_ATOMIC_ACCESSES__
 `define __AMBA_AXI4_ATOMIC_ACCESSES__
package amba_axi4_atomic_accesses;
   /*		 ><><><><><><><><><><><><><><><><><><><><             *
    *		 Section A7.2 Exclusive accesses                      *
    *		 ><><><><><><><><><><><><><><><><><><><><	      */

   /* ,         ,                                                     *
    * |\\\\ ////|  "The exclusive access mechanism can provide        *
    * | \\\V/// |   semaphore-type operations without requiring the   *
    * |	 |~~~|	|   bus to remain dedicated to a particular master    *
    * |	 |===|	|   for the duration of the operation.                *
    * |	 |A  |	|   The AxLOCK signals select exclusive access".      *
    * |	 | X |	|   Ref: A7.2 Exclusive accesses, pA7-96, Table A7-2. *
    *  \ |  I| /	 A7.4 Atomic access signaling, pA7-100.       *
    *	\|===|/							      *
    *	 '---'							      */
   property exclusive_access(valid, ready, axlock);
      valid && ready && axlock == EXCLUSIVE;
   endproperty // exclusive_access

   /*		 ><><><><><><><><><><><><><><><><><><><><             *
    *		 Section A7.4 Atomic access signaling                 *
    *		 ><><><><><><><><><><><><><><><><><><><><	      */

   /* ,         ,                                                     *
    * |\\\\ ////|  "AXI4 removes the support for locked transactions  *
    * | \\\V/// |   and uses only a 1-bit lock signal. Table A7-2     *
    * |	 |~~~|	|   shows the AXI4 signal encoding of the AxLOCK      *
    * |	 |===|	|   signals".                                         *
    * |	 |A  |	|   Ref: A7.4 Atomic access signaling, pA7-100,       *
    * |	 | X |	|        Table A7-2.                                  *
    *  \ |  I| /                  				      *
    *	\|===|/							      *
    *	 '---'							      */
   property normal_access(valid, ready, axlock);
      valid && ready && axlock == NORMAL;
   endproperty // normal_access
endpackage // amba_axi4_single_transaction_attributes
`endif

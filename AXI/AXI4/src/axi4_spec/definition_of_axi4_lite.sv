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
`ifndef __DEFINITION_OF_AXI4_LITE__
 `define __DEFINITION_OF_AXI4_LITE__
package definition_of_axi4_lite;
   /*		 ><><><><><><><><><><><><><><><><><><><><             *
    *		 Section B1.1: Definition of AXI4-Lite                *
    *		 ><><><><><><><><><><><><><><><><><><><><	      */

   /* ,         ,                                                     *
    * |\\\\ ////|  "All data accesses use the full width of the data  *
    * | \\\V/// |   bus.                                              *
    * |	 |~~~|	|   AXI4-Lite supports a data bus width of 32-bit     *
    * |	 |===|	|   or 64-bit".                                       *
    * |	 |A  |	|   Ref: B1.1 Definition of AXI4-Lite, pB1-126        *
    * |	 | X |	|						      *
    *  \ |  I| /						      *
    *	\|===|/							      *
    *	 '---'							      */
   property axi4l_databus_width(data_width);
      data_width inside {32, 64};
   endproperty // exit_from_reset
   
   /* ,         ,                                                     *
    * |\\\\ ////|  "The EXOKAY response is not supported on the read  *
    * | \\\V/// |   data and write response channels".                *
    * |	 |~~~|	|   Ref: B1.1.1 Signal List, pB1-126.                 *
    * |	 |===|	|                                                     *
    * |	 |A  |	|                                                     *
    * |	 | X |	|						      *
    *  \ |  I| /						      *
    *	\|===|/							      *
    *	 '---'							      */
   property unsupported_transfer_status(valid, response, value);
      valid |-> response != value;
   endproperty // unsupported_transfer_status
endpackage // definition_of_axi4_lite
`endif //  `ifndef __DEFINITION_OF_AXI4_LITE__

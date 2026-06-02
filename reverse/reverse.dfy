/*
 * This is the skeleton for your line reverse utility.
 *
 */

include "Io.dfy"

method {:main} Main(ghost env: HostEnvironment?)
  requires env != null && env.Valid() && env.ok.ok()
  modifies env.ok
  modifies env.files
{
    print "TODO!\n";
}

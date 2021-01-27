------------------------------- CONFIG EWD998_anim -------------------------------
CONSTANTS
    N = 5

SPECIFICATION 
    Spec

ALIAS
    Alias

INVARIANT 
    AnimInv
==================================================================================

------------------------------- MODULE EWD998_anim -------------------------------
EXTENDS EWD998, SVG, TLC \* Grab SVG from https://github.com/tlaplus/CommunityModules/

IsSend ==
    \* These are exactly the two variables changed by SendMessage and by SM only.
    /\ counter # counter'
    /\ pending # pending'
    /\ UNCHANGED <<color, token, active>>

From == 
    CHOOSE i \in DOMAIN counter: counter[i] # counter[i]'

To ==
    CHOOSE i \in DOMAIN pending: pending[i] # pending[i]'

---------------------------------------------------------------------------

Arial == [font |-> "Arial"]

LegendBasePos == [ x |-> -5, y |-> 25 ]

RingBasePos == [w |-> 55, h |-> 55, r |-> 75]

\* 12pts (x/y) offset to be concentric with RingNetwork.
TokenBasePos == [ w |-> RingBasePos.w + 12, 
                  h |-> RingBasePos.h + 12,
                  r |-> RingBasePos.r + 25 ]

---------------------------------------------------------------------------
\* Labels

Labels == Group(<<Text(LegendBasePos.x, LegendBasePos.y, "Circle: Active, Black: Tainted", Arial),
                  Text(LegendBasePos.x, LegendBasePos.y + 20, "Line: Message, Dot: Receiver", Arial),
                  Text(LegendBasePos.x, LegendBasePos.y + 40, "Level: " \o ToString(TLCGet("level")), Arial)>>,
                  <<>>)

---------------------------------------------------------------------------
NodeDimension == 26

\* Ring Network
RingNetwork ==
    LET RN[ n \in Node ] ==         
            LET coord == NodeOfRingNetwork(RingBasePos.w, RingBasePos.h, RingBasePos.r, n, N)    
                id == Text(coord.x + 10, coord.y - 5, ToString(n), Arial)
                node == Rect(coord.x, coord.y, NodeDimension, NodeDimension,
                                            \* round (rx=15) if node is active.
                                            [rx |-> IF ~active[n] THEN "0" ELSE "15",
                                            stroke |-> "black", 
                                            fill |-> color[n]])
            IN Group(<<node, id>>, ("transform" :> "translate(0 125)"))
    IN Group(RN, <<>>)

---------------------------------------------------------------------------
\* Token ring (with larger radius than ring above and only for the node that currently holds the token).
TokenNetwork ==     
    LET coord == NodeOfRingNetwork(TokenBasePos.w, TokenBasePos.h, TokenBasePos.r, token.pos, N)    
        circ  == Circle(coord.x, coord.y, 8, [stroke |-> "black", fill |-> token.color])
        id    == Text(coord.x - 3, coord.y + 3, ToString(token.q), 
           [font |-> "Arial", fill |-> IF token.color = "black" THEN "white" ELSE "black" ])
    \* Group always expects a sequence!
    IN Group(<<circ, id>>, ("transform" :> "translate(0 125)"))

---------------------------------------------------------------------------
\* Messages send from one node to another.  A proper arrow would be more intuitive with regards to the direction
\* of message flow but SVG doesn't natively has arrows.  This is why we use a lollipop instead where the ball
\* replaces the arrowhead. 

\* Centers the line/circle at the center of a node instead of
\* a node's left upper corner (which are its 0:0 coordinates).
ArrowPosOffset == NodeDimension \div 2

Messages ==
    LET from == NodeOfRingNetwork(RingBasePos.w, RingBasePos.h, RingBasePos.r, From, N)
        to   == NodeOfRingNetwork(RingBasePos.w, RingBasePos.h, RingBasePos.r, To, N)
        circ == Circle(to.x + ArrowPosOffset, to.y + ArrowPosOffset, 3, 
                        [stroke |-> "orange", fill |-> "orange"])  
        line == Line(from.x + ArrowPosOffset, from.y + ArrowPosOffset, 
                        to.x + ArrowPosOffset, to.y + ArrowPosOffset, 
                        [stroke |-> "orange"])
    IN Group(IF IsSend THEN <<line, circ>> ELSE <<>>, ("transform" :> "translate(0 125)"))

---------------------------------------------------------------------------
Animation == SVGElemToString(Group(<<Labels, RingNetwork, TokenNetwork, Messages>>, <<>>))

Alias == [ 
    \* toolbox |-> Animation,
    eyeofgnome |-> "<svg viewBox='-80 0 300 300'>" \o Animation \o "</svg>"
    \* foob |-> [i \in 1..20 |-> i]
    ]

---------------------------------------------------------------------------

\* Property that leads to interesting traces when animated.

AnimInv == terminationDetected => TLCGet("level") < 20 

=============================================================================

## Assuming the most recent Toolbox nightly build (https://nightly.tlapl.us/dist)
## installed to /opt/toolbox.  On macOS, install gawk with `brew install gawk` 
## (default nawk does not like the match).

/opt/toolbox/tla2tools.jar -simulate -noGenerateSpecTE EWD998_anim | gawk 'match($0,/<svg.*<\/svg>/) { n += 1; print substr($0,RSTART,RLENGTH) > sprintf("%03d", n) ".svg" }' && eog .


## The best viewer for a stack of SVGs is Gnome's Eye Of Gnome (eog) that
## is available for Win, macOS, and Linux.  In its preferences, one can replace
## the transparent background with a custom color. One can also run a slideshow
## with a custom frame rate.

----

## Unfortunately, the MacPorts package cannot be installed
## because of a broken dependency (https://trac.macports.org/ticket/61713).  Instead,
## one can use the browser-based TLA+ trace Animator at https://animator.tlapl.us.
## In this case, a slightly different awk matching is needed.  Optionally, pipe
## output of awk directly to xclip to send it to the clipboard ("| xclip").

/opt/toolbox/tla2tools.jar -simulate EWD998_anim | gawk 'match($0,/toolbox = .*/) { print "[\ntb |->" substr($0, RSTART+9, RLENGTH) "\n]," }'

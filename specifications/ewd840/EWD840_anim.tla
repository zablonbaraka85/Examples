------------------------------- MODULE EWD840_anim -------------------------------
EXTENDS EWD840, SVG \* Grab SVG from https://github.com/tlaplus/CommunityModules/

\* In order to show messages, we need a (auxiliary) history variable to remember
\* the occurrence of a SendMsg step including the sender and receiver of a message.
\* The spec below is equivalent to EWD840 except for the history variable, and 
\* AnimInit more constraint to reduce the number of initial states.
VARIABLES history

AnimInit == 
  /\ active \in [Nodes -> BOOLEAN]
  /\ color \in [Nodes -> Color]
  /\ tpos = N - 1 \* The token is initially always at N - 1.
  /\ tcolor = "black"
  /\ history = <<0, 0, "init">>
  
AnimInitiateProbe ==
  /\ InitiateProbe
  /\ history' = <<history[1], history[2], "InitiateProbe">>
  
AnimPassToken(i) == 
  /\ PassToken(i)
  /\ history' = <<history[1], history[2], "PassToken">>

AnimSystem == 
  /\ AnimInitiateProbe \/ \E i \in Nodes \ {0} : AnimPassToken(i)

AnimSendMsg(i) ==
  /\ active[i]
  /\ \E j \in Nodes \ {i} :
        /\ active' = [active EXCEPT ![j] = TRUE]
        /\ color' = [color EXCEPT ![i] = IF j>i THEN "black" ELSE @]
        /\ history' = <<i, j, "SendMsg">>
  /\ UNCHANGED <<tpos, tcolor>>

AnimDeactivate(i) ==
  /\ Deactivate(i)
  /\ history' = <<history[1], history[2], "Deactivate">>

AnimEnvironment == \E i \in Nodes : AnimSendMsg(i) \/ AnimDeactivate(i)
                  
AnimNext == AnimSystem \/ AnimEnvironment

Animvars == <<active, color, tpos, tcolor, history>>

AnimSpec == AnimInit /\ [][AnimNext]_Animvars /\ WF_Animvars(AnimSystem)

---------------------------------------------------------------------------
Arial == [font |-> "Arial"]

LegendBasePos == [ x |-> 5, y |-> 25 ]

RingBasePos == [w |-> 55, h |-> 55, r |-> 75]

\* 12pts (x/y) offset to be concentric with RingNetwork.
TokenBasePos == [ w |-> RingBasePos.w + 12, 
                  h |-> RingBasePos.h + 12,
                  r |-> RingBasePos.r + 25 ]

---------------------------------------------------------------------------
\* Labels

GLegend == Text(LegendBasePos.x - 75, LegendBasePos.y, "Circle: Active, Line: Message, Dot: Receiver, Black: Tainted", Arial)

GLevel == Group(<<Text(LegendBasePos.x, LegendBasePos.y + 15, "Level:", Arial), 
                  Text(LegendBasePos.x + 55, LegendBasePos.y + 15, ToString(TLCGet("level")), Arial)>>,
                  <<>>)

Labels == Group(<<GLevel, GLegend>>, <<>>)

---------------------------------------------------------------------------
NodeDimension == 26

\* Ring Network
RingNetwork ==
    LET RN[ n \in Nodes ] ==         
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
    LET coord == NodeOfRingNetwork(TokenBasePos.w, TokenBasePos.h, TokenBasePos.r, tpos, N)    
        circ  == Circle(coord.x, coord.y, 5, [stroke |-> "black", fill |-> tcolor])  
    \* Group always expects a sequence!
    IN Group(<<circ>>, ("transform" :> "translate(0 125)"))

---------------------------------------------------------------------------
\* Messages send from one node to another.  A proper arrow would be more intuitive with regards to the direction
\* of message flow but SVG doesn't natively has arrows.  This is why we use a lollipop instead where the ball
\* replaces the arrowhead. 

\* Centers the line/circle at the center of a node instead of
\* a node's left upper corner (which are its 0:0 coordinates).
ArrowPosOffset == NodeDimension \div 2

Messages ==
    LET visible == IF history[3] = "SendMsg" THEN "visible" ELSE "hidden"
        from == NodeOfRingNetwork(RingBasePos.w, RingBasePos.h, RingBasePos.r, history[1], N)
        to   == NodeOfRingNetwork(RingBasePos.w, RingBasePos.h, RingBasePos.r, history[2], N)
        circ == Circle(to.x + ArrowPosOffset, to.y + ArrowPosOffset, 3, 
                        [stroke |-> "orange", fill |-> "orange", visibility |-> visible])  
        line == Line(from.x + ArrowPosOffset, from.y + ArrowPosOffset, 
                        to.x + ArrowPosOffset, to.y + ArrowPosOffset, 
                        [stroke |-> "orange", visibility |-> visible])
    IN Group(<<line, circ>>, ("transform" :> "translate(0 125)"))

---------------------------------------------------------------------------
Animation == SVGElemToString(Group(<<Labels, RingNetwork, TokenNetwork, Messages>>, <<>>))

Alias == [ anim |-> 
"<svg viewBox='-80 0 300 300'>" \o Animation \o "</svg>"]

---------------------------------------------------------------------------

\* Property that leads to interesting traces when animated.

AnimInv == terminationDetected => TLCGet("level") < 20 

=============================================================================

## Check the spec with `Alias` configured as `ALIAS` in EWD840_anim.cfg.
## Remove the ugly qoutes are the chars that represent the elements in the
## buffer with sed.
/opt/toolbox/tla2tools.jar -simulate EWD840_anim | sed 's/\\"//g' | awk 'match($0,/<svg.*<\/svg>/) { n += 1; print substr($0,RSTART,RLENGTH) > n ".svg" }'

## The best viewer for a stack of SVGs is Gnome's Eye Of Gnome (eog) that
## is available for Win, macOS, and Linux.  In its preferences, one can replace
## the transparent background with a custom color. One can also run a slideshow
## with a custom frame rate.

----
## The commands below here have multiple issues such as broken aspect ratio,
## wrong dimensions, ...  Most importantly though, inkscape *ignores* the 
## visibility attribute causing a bogus animation.

## The svgs have transparent background.  Convert them into pngs with a
## suitable resolution for the video while adding a white background.
for i in *.svg; do convert -density 1000 -resize 1920x1080 $i $i.png; done

## contrary to convert above, this replaces the transparent background
## with a lightyellow one.
## THIS IS BROKEN!!!  Handling of the visibility tag in SVG is broken causing
## visibility=hidden to be ignored:
## - https://gitlab.com/inkscape/inbox/-/issues/2177
## - https://bugs.launchpad.net/inkscape/+bug/166042
## - https://bugs.launchpad.net/inkscape/+bug/1577763
for i in *.svg; do inkscape -w 1920 -h 1920 -b lightyellow --export-png=$i.png $i; done

## Render the sequence of pngs into an mp4 with two frames per second. 
ffmpeg -r 2 -y -i %d.svg.png EWD840.mp4


## https://stackoverflow.com/a/25002372/6291195 partially gets the job done of
## rendering an mp4 from the stack of SVGs.  It replaces the transparent background
## with a white one, but the dimensions are screwed up
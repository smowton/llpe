---
layout: page
title: Developer Documentation - GUI
permalink: /devdocs-gui/
---

LLPE's gui is implemented in the `driver` pass. It runs the master analysis pass and then presents the results in a graphical format, using DOT representations of specialisation results to illustrate what specialisation was possible and make clear where barriers to specialsiation, such as writes through unknown pointers, can be found. It is implemented primarily in `driver/Integrator.cpp`, and uses wxWidgets to provide its GUI.

The user can manually enable or disable certain specialisation contexts, determining whether specialised variants will be emitted or not. Per default the decision is taken using a simple heuristic based on the total number of eliminated and residual instructions that will result from committing a particular context.
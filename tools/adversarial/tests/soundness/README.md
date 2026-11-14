These published witnesses are copied from the MIT-0 licensed
[Shenanigans corpus](https://github.com/VladimirReshetnikov/Shenanigans),
revision `abe6dafb2e9ed28f643ac464db01b8876210e4d1` (see test sources for
issue references). The accompanying LICENSE applies to these files.

The tests require the expected compiler or checker diagnostic, not merely a
nonzero exit, so that missing dependencies do not count as rejection. They
cover a selection of published soundness bugs and are not an exhaustive proof
of kernel soundness. Upstream's `dev/doc/critical-bugs.md` documents additional
issues, including unresolved cases.

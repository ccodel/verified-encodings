# Verified encodings in Lean

This is a project by [Cayden Codel](http://www.crcodel.com), advised by [Jeremy Avigad](https://www.andrew.cmu.edu/user/avigad/) and [Marijn Heule](https://www.cs.cmu.edu/~mheule/). It intends to formally verify encodings of logic gates, cardinality constraints, and other methods of specifying mathematical problems in propositional logic.

#### Building locally

You can install Lean following the instructions at [https://leanprover-community.github.io/get_started.html#regular-install](https://leanprover-community.github.io/get_started.html#regular-install).

Assuming you have Lean installed, you can fetch and build this repository as follows:

```bash
  leanproject get ccodel/verified-encodings
  cd verified-encodings
  leanproject build
```
You can then open folder in VS Code and browse the files.

### Gitpod

If you have an account with Gitpod, you can instead browse the repository in your browser, running Lean in the cloud.

[![Open in Gitpod](https://gitpod.io/button/open-in-gitpod.svg)](https://gitpod.io/#https://github.com/ccodel/verified-encodings)

If you don't have an account with Gitpod, clicking the button will prompt you to create one.

Gitpod offers 50 free hours of workspace time every month. When you are done, choose "Stop workspace" from the menu in the upper left corner to stop the clock. Alternatively, Gitpod will stop it for you after 30 minutes, or 3 minutes after you close the browser window or tab.

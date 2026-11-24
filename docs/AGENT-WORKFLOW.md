# Building a game with agents: Pi + OptChat

Bend Grounds was built with AI agents working in **Pi + OptChat**, with Aleksandr Podgaiko steering the project, choosing priorities and making the final calls. Agents wrote most of the implementation. Aleksandr describes OptChat as drawing on Victor Taelin's ideas; this is his understanding of the inspiration, not a claim of Taelin's participation in or endorsement of this project.

The useful artifact is the [playable game](../README.md), not the number of agents involved. One Bend 2 engine supplies the rules for browser play, native bots and external agent clients.

## What the workflow looked like

- **Parallel work, explicit ownership.** Bounded tasks went to separate agents—for example, engine investigation, API checks, documentation and release-safety review. One owner integrated shared artifacts rather than having several agents edit the same thing.
- **A lead that integrated, not just delegated.** Reports were inputs to decisions, not automatic acceptance. The lead checked consequential claims against source, command output or the running application.
- **Independent perspectives.** Codex and Claude reviewed the same frozen, sanitized release snapshot. Their findings led to fixes; agreement between models was not treated as a test result.
- **Real execution at the end of the chain.** Before the first public release, the work included native builds, API regressions, scoped Bend proof checks and an actual browser playthrough. These establish different things; none substitutes for all the others.
- **A deliberately small public release.** The research workspace was not published wholesale. The release uses a fresh history and selected source, documentation and screenshots, without private run logs or cloud credentials.

## What did not work—and why that matters

The project also explored learned game policies. That effort did **not** establish a stronger learned player; this repository does not ship a successful RL trainer or a trained LLM opponent. **Rook is a native heuristic bot.** The [agent interface](AGENTS-API.md) is available for other experiments.

The clearest process failure was spending too long on local mocks and validation machinery before exercising critical interfaces on the actual target runtime. A local PASS validated the implementation against assumed platform behavior, not the real platform itself. The better sequence was a minimal real vertical slice first, then tests around observed failures.

Another lesson: a background task is not a reliable autonomous workflow merely because it was launched. Completion needs a working route back to the responsible agent, followed by result verification and the next decision. Host sleep, lost connectivity and missing callbacks remained real limits—not problems solved by adding more agents.

## Why this might interest agent-tool builders

This project exercised the unglamorous parts of long-running agent work: ownership across handoffs, separating reports from evidence, preserving failed attempts, returning after background work, and stopping a research branch without losing the useful product.

The takeaway is not “agents built a game unattended.” A human-directed agent workflow produced a playable application, while an ambitious learning experiment failed to demonstrate its intended gain. Both outcomes belong in the account.

This is a retrospective, not a benchmark of Pi or OptChat, a reproducible agent-orchestration package, or a claim that every stage ran with the same configuration.

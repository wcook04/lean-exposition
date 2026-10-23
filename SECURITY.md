# Security

This local tool does not sandbox Lean. Only execute trusted source and inspect its
package configuration first. Comparator uses the sandbox supported by its own
version; the normal wrapper never disables it. Do not paste credentials into source
files or command arguments.

This repository has no public issue tracker or security contact yet. During local
development, report a security concern directly to the person who supplied the
checkout. Before any public release, the maintainer must provide a private reporting
route. Do not publish credentials, exploit payloads involving private data, or
unreviewed source snapshots in a public report.

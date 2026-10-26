# Security

This local tool does not sandbox Lean. Only execute trusted source and inspect its
package configuration first. Comparator uses the sandbox supported by its own
version; the normal wrapper never disables it. Do not paste credentials into source
files or command arguments.

Report vulnerabilities through [GitHub private vulnerability reporting](https://github.com/wcook04/lean-exposition/security/advisories/new).
Include the affected revision, a minimal reproduction and the expected behaviour.
Keep credentials, private data and unpublished source snapshots out of public issues
and pull requests.

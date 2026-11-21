// A page that throws while drawing shows one line in its place, with the header still there, rather
// than blanking the whole site. The error is reported to the console for whoever is checking.
import { Component, type ReactNode } from "react";

export class PageGuard extends Component<{ view: string; children: ReactNode }, { failed: string | null }> {
  state = { failed: null as string | null };

  static getDerivedStateFromError(error: unknown) {
    return { failed: error instanceof Error ? error.message : String(error) };
  }

  componentDidCatch(error: unknown) {
    console.error(`The ${this.props.view} view failed to draw:`, error);
  }

  componentDidUpdate(previous: { view: string }) {
    if (previous.view !== this.props.view && this.state.failed) this.setState({ failed: null });
  }

  render() {
    if (this.state.failed)
      return (
        <p className="page-guard" role="alert">
          This view could not be drawn ({this.state.failed}). The paper and the other views still work.
        </p>
      );
    return this.props.children;
  }
}

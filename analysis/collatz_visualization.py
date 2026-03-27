#!/usr/bin/env python3
"""
Collatz Orbit Visualization Script.

Generates publication-quality figures for the Collatz orbit analysis
based on the Syracuse map on ZMod structures.

Figures produced:
  1. ZMod 13 transition graph
  2. ZMod 104 (13*8) transition graph (odd residues only)
  3. Bad streak length vs modulus parameter k
  4. Convergence window analysis (cumulative drift vs window size)
  5. v2 distribution across k values
  6. Worst-case drift paths for k=3, k=4
"""

import json
import os
import math
from collections import defaultdict
from fractions import Fraction

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
import networkx as nx
import numpy as np

# ---------------------------------------------------------------------------
# Paths
# ---------------------------------------------------------------------------
SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
RESULTS_PATH = os.path.join(SCRIPT_DIR, "results.json")
FIGURES_DIR = os.path.join(SCRIPT_DIR, "figures")
os.makedirs(FIGURES_DIR, exist_ok=True)

# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------
LOG2_3 = Fraction(1585, 1000)  # approximation for DP drift computation
LOG2_3_FLOAT = math.log2(3)

# ---------------------------------------------------------------------------
# Utility helpers
# ---------------------------------------------------------------------------

def v2(n):
    """Return the 2-adic valuation of n."""
    if n == 0:
        return -1
    return (n & -n).bit_length() - 1


def load_results():
    """Load the analysis results JSON."""
    with open(RESULTS_PATH) as f:
        return json.load(f)


def edge_color_for_v2(v2_val):
    """Return color based on v2 value: red=1 (bad), blue=2 (good), green=3+."""
    if v2_val == 1:
        return "#d62728"   # red
    elif v2_val == 2:
        return "#1f77b4"   # blue
    else:
        return "#2ca02c"   # green


def edge_alpha_for_v2(v2_val):
    """Return alpha transparency."""
    if v2_val == 1:
        return 0.85
    elif v2_val == 2:
        return 0.7
    else:
        return 0.6


# ---------------------------------------------------------------------------
# Style setup
# ---------------------------------------------------------------------------

def setup_style():
    """Configure matplotlib for publication-quality output."""
    try:
        plt.style.use("seaborn-v0.8-whitegrid")
    except OSError:
        try:
            plt.style.use("seaborn-whitegrid")
        except OSError:
            plt.style.use("ggplot")
    plt.rcParams.update({
        "font.size": 11,
        "axes.titlesize": 13,
        "axes.labelsize": 12,
        "xtick.labelsize": 10,
        "ytick.labelsize": 10,
        "legend.fontsize": 10,
        "figure.dpi": 150,
        "savefig.dpi": 200,
        "savefig.bbox": "tight",
        "savefig.pad_inches": 0.15,
    })


# ===========================================================================
# Figure 1: ZMod 13 Transition Graph
# ===========================================================================

def fig1_zmod13_transitions(results):
    """Circular layout graph of the Syracuse map on ZMod 13."""
    print("  Generating: zmod13_transitions.png")

    data = results["part1"]
    odd_residues = data["odd_residues"]  # [1,3,5,7,9,11]
    images = data["images"]             # str(r) -> str(v2) -> image

    G = nx.MultiDiGraph()
    for node in range(13):
        G.add_node(node)

    # Place nodes on a circle
    angles = {i: 2 * math.pi * i / 13 - math.pi / 2 for i in range(13)}
    pos = {i: (1.8 * math.cos(angles[i]), 1.8 * math.sin(angles[i])) for i in range(13)}

    # For the ZMod 13 graph, each odd residue r has an image for each v2 value.
    # We show only v2 = 1, 2, 3 as representative edges (the most common ones).
    edges = []
    for r in odd_residues:
        r_str = str(r)
        for v2_val in [1, 2, 3]:
            v2_str = str(v2_val)
            target = images[r_str][v2_str]
            edges.append((r, target, v2_val))

    fig, ax = plt.subplots(figsize=(10, 10))
    ax.set_aspect("equal")
    ax.set_title("Syracuse Map on ZMod 13\nTransition Graph (edges for v$_2$ = 1, 2, 3)",
                 fontsize=14, fontweight="bold", pad=15)

    # Draw nodes
    node_colors = []
    for i in range(13):
        if i in odd_residues:
            node_colors.append("#ff9800")   # orange for odd residues
        elif i == 0:
            node_colors.append("#9e9e9e")   # gray for 0
        else:
            node_colors.append("#e0e0e0")   # light gray for even
    node_sizes = [900 if i in odd_residues else 500 for i in range(13)]

    nx.draw_networkx_nodes(G, pos, ax=ax,
                           nodelist=list(range(13)),
                           node_color=node_colors,
                           node_size=node_sizes,
                           edgecolors="black", linewidths=1.5)

    nx.draw_networkx_labels(G, pos, ax=ax,
                            labels={i: str(i) for i in range(13)},
                            font_size=11, font_weight="bold")

    # Draw edges with curvature to distinguish parallel edges
    drawn_pairs = defaultdict(int)
    for src, tgt, v2_val in edges:
        pair_key = (min(src, tgt), max(src, tgt))
        idx = drawn_pairs[pair_key]
        drawn_pairs[pair_key] += 1

        color = edge_color_for_v2(v2_val)
        width = 0.8 + v2_val * 0.6
        alpha = edge_alpha_for_v2(v2_val)

        if src == tgt:
            # Self-loop
            cx, cy = pos[src]
            angle = angles[src]
            loop_size = 0.2 + idx * 0.08
            circle = mpatches.FancyArrowPatch(
                (cx + loop_size * math.cos(angle),
                 cy + loop_size * math.sin(angle)),
                (cx + loop_size * math.cos(angle + 0.1),
                 cy + loop_size * math.sin(angle + 0.1)),
                connectionstyle=f"arc3,rad=1.5",
                arrowstyle="-|>", mutation_scale=12,
                color=color, linewidth=width, alpha=alpha)
            ax.add_patch(circle)
        else:
            rad = 0.15 + idx * 0.12
            if src > tgt:
                rad = -rad
            arrow = mpatches.FancyArrowPatch(
                pos[src], pos[tgt],
                connectionstyle=f"arc3,rad={rad}",
                arrowstyle="-|>", mutation_scale=15,
                color=color, linewidth=width, alpha=alpha,
                shrinkA=15, shrinkB=15)
            ax.add_patch(arrow)

    # Legend
    legend_elements = [
        mpatches.Patch(color="#d62728", label="v$_2$ = 1 (bad)"),
        mpatches.Patch(color="#1f77b4", label="v$_2$ = 2 (good)"),
        mpatches.Patch(color="#2ca02c", label="v$_2$ = 3+ (very good)"),
        mpatches.Patch(facecolor="#ff9800", edgecolor="black", label="Odd residue"),
        mpatches.Patch(facecolor="#e0e0e0", edgecolor="black", label="Even residue"),
    ]
    ax.legend(handles=legend_elements, loc="lower left", fontsize=10,
              framealpha=0.9)

    ax.set_xlim(-2.8, 2.8)
    ax.set_ylim(-2.8, 2.8)
    ax.axis("off")
    fig.savefig(os.path.join(FIGURES_DIR, "zmod13_transitions.png"))
    plt.close(fig)


# ===========================================================================
# Figure 2: ZMod 104 (13x8) Transition Graph
# ===========================================================================

def build_transition_graph(k_exp):
    """Build Syracuse transition graph on ZMod(13 * 2^k_exp)."""
    modulus = 13 * (1 << k_exp)
    transitions = {}
    for r in range(modulus):
        if r % 2 == 0:
            continue
        val = 3 * r + 1
        vv = v2(val)
        image = (val >> vv) % modulus
        transitions[r] = (vv, image)
    return modulus, transitions


def fig2_zmod104_transitions(results):
    """Spring-layout graph for ZMod 104 showing odd residues."""
    print("  Generating: zmod104_transitions.png")

    modulus, transitions = build_transition_graph(3)

    G = nx.DiGraph()
    for r in transitions:
        G.add_node(r)

    edge_list = []
    for r, (vv, image) in transitions.items():
        G.add_edge(r, image, v2=vv)
        edge_list.append((r, image, vv))

    # Find bad streak chains (consecutive v2=1 edges)
    bad_streak_edges = set()
    for r in transitions:
        if transitions[r][0] == 1:
            chain = []
            node = r
            visited = set()
            while node in transitions and transitions[node][0] == 1 and node not in visited:
                visited.add(node)
                _, nxt = transitions[node]
                chain.append((node, nxt))
                node = nxt
            if len(chain) >= 2:
                for e in chain:
                    bad_streak_edges.add(e)

    pos = nx.spring_layout(G, k=2.5, iterations=80, seed=42)

    fig, ax = plt.subplots(figsize=(14, 14))
    ax.set_title("Syracuse Map on ZMod 104 (= 13 $\\times$ 8)\nOdd Residues Only, Spring Layout",
                 fontsize=14, fontweight="bold", pad=15)

    # Draw nodes -- color by v2 of outgoing edge
    node_colors = []
    for r in G.nodes():
        vv = transitions[r][0]
        if vv == 1:
            node_colors.append("#ffcccc")  # light red
        elif vv == 2:
            node_colors.append("#cce5ff")  # light blue
        else:
            node_colors.append("#ccffcc")  # light green

    nx.draw_networkx_nodes(G, pos, ax=ax,
                           node_color=node_colors,
                           node_size=200,
                           edgecolors="gray", linewidths=0.5)

    # Draw edges
    for src, tgt, vv in edge_list:
        is_bad_chain = (src, tgt) in bad_streak_edges
        color = edge_color_for_v2(vv)
        width = 2.5 if is_bad_chain else (0.5 + vv * 0.4)
        alpha = 0.95 if is_bad_chain else 0.4
        style = "solid"

        arrow = mpatches.FancyArrowPatch(
            pos[src], pos[tgt],
            connectionstyle="arc3,rad=0.1",
            arrowstyle="-|>", mutation_scale=8,
            color=color, linewidth=width, alpha=alpha,
            shrinkA=6, shrinkB=6, linestyle=style)
        ax.add_patch(arrow)

    # Node labels for important nodes (bad streak starts)
    bad_start_labels = {}
    for r in transitions:
        vv = transitions[r][0]
        if vv == 1:
            # Check if this starts a streak of length >= 3
            streak_len = 0
            node = r
            visited = set()
            while node in transitions and transitions[node][0] == 1 and node not in visited:
                visited.add(node)
                streak_len += 1
                _, node = transitions[node]
            if streak_len >= 3:
                bad_start_labels[r] = str(r)

    if bad_start_labels:
        nx.draw_networkx_labels(G, pos, labels=bad_start_labels, ax=ax,
                                font_size=7, font_color="darkred", font_weight="bold")

    legend_elements = [
        mpatches.Patch(color="#d62728", label="v$_2$ = 1 (bad)"),
        mpatches.Patch(color="#1f77b4", label="v$_2$ = 2 (good)"),
        mpatches.Patch(color="#2ca02c", label="v$_2$ = 3+ (very good)"),
        plt.Line2D([0], [0], color="#d62728", linewidth=3, label="Bad streak chain"),
    ]
    ax.legend(handles=legend_elements, loc="lower left", fontsize=10, framealpha=0.9)

    ax.axis("off")
    fig.savefig(os.path.join(FIGURES_DIR, "zmod104_transitions.png"))
    plt.close(fig)


# ===========================================================================
# Figure 3: Bad Streak Length vs k
# ===========================================================================

def fig3_bad_streaks_vs_k(results):
    """Bar chart of max bad streak length for each k."""
    print("  Generating: bad_streaks_vs_k.png")

    part3 = results["part3"]
    ks = sorted(int(k) for k in part3.keys())
    max_streaks = [part3[str(k)]["max_bad_streak"] for k in ks]

    fig, ax = plt.subplots(figsize=(8, 5))

    bars = ax.bar(ks, max_streaks, color="#5c6bc0", width=0.6, edgecolor="white",
                  linewidth=1.2, zorder=3, label="Max bad streak length")

    # Annotate bars
    for bar, val in zip(bars, max_streaks):
        ax.text(bar.get_x() + bar.get_width() / 2, bar.get_height() + 0.15,
                str(val), ha="center", va="bottom", fontweight="bold", fontsize=12)

    # Reference line: k+1
    k_plus_1 = [k + 1 for k in ks]
    ax.plot(ks, k_plus_1, "o--", color="#e53935", linewidth=2, markersize=7,
            label="$k + 1$ (pattern)", zorder=4)

    ax.set_xlabel("Parameter $k$ (modulus = 13 $\\times$ 2$^k$)")
    ax.set_ylabel("Maximum Bad Streak Length")
    ax.set_title("Maximum Bad Streak Length vs. $k$", fontweight="bold")
    ax.set_xticks(ks)
    ax.set_xticklabels([f"$k={k}$" for k in ks])
    ax.legend(loc="upper left", framealpha=0.9)
    ax.set_ylim(0, max(max_streaks) + 2)
    ax.grid(axis="y", alpha=0.4)

    fig.savefig(os.path.join(FIGURES_DIR, "bad_streaks_vs_k.png"))
    plt.close(fig)


# ===========================================================================
# Figure 4: Convergence Window Analysis
# ===========================================================================

def fig4_convergence_windows(results):
    """Plot worst-case cumulative drift vs window size W for each k."""
    print("  Generating: convergence_windows.png")

    part3 = results["part3"]
    ks = sorted(int(k) for k in part3.keys())

    colors_map = {
        3: "#1f77b4",
        4: "#ff7f0e",
        5: "#2ca02c",
        6: "#d62728",
        7: "#9467bd",
        8: "#8c564b",
    }

    fig, ax = plt.subplots(figsize=(12, 6))

    for k in ks:
        info = part3[str(k)]
        drifts = info["window_drifts"]
        ws = sorted(int(w) for w in drifts.keys())
        drift_vals = [drifts[str(w)] for w in ws]

        color = colors_map.get(k, "gray")
        ax.plot(ws, drift_vals, "-", color=color, linewidth=2, label=f"$k = {k}$",
                alpha=0.85)

        # Find and mark convergence point (first negative crossing)
        conv_w = info.get("convergence_window")
        if conv_w is not None:
            conv_drift = drifts[str(conv_w)]
            ax.plot(conv_w, conv_drift, "v", color=color, markersize=10,
                    markeredgecolor="black", markeredgewidth=1, zorder=5)
            ax.annotate(f"$W={conv_w}$",
                        xy=(conv_w, conv_drift),
                        xytext=(conv_w + 1.5, conv_drift + 0.8),
                        fontsize=9, color=color, fontweight="bold",
                        arrowprops=dict(arrowstyle="->", color=color, lw=1))

    # Horizontal line at drift = 0
    ax.axhline(y=0, color="black", linewidth=1.5, linestyle="--", alpha=0.7, zorder=2)
    ax.fill_between([0, 55], 0, -20, alpha=0.05, color="green")
    ax.fill_between([0, 55], 0, 12, alpha=0.05, color="red")

    ax.text(48, -1.5, "Convergent\n(drift < 0)", fontsize=9, color="green",
            ha="center", style="italic", alpha=0.8)
    ax.text(48, 1.5, "Divergent\n(drift > 0)", fontsize=9, color="red",
            ha="center", style="italic", alpha=0.8)

    ax.set_xlabel("Window Size $W$ (number of Syracuse steps)")
    ax.set_ylabel("Worst-case Cumulative Drift (bits)")
    ax.set_title("Convergence Window Analysis\nWorst-case Drift over $W$-step Windows",
                 fontweight="bold")
    ax.legend(loc="upper right", framealpha=0.9, ncol=2)
    ax.set_xlim(0, 52)
    ax.grid(alpha=0.3)

    fig.savefig(os.path.join(FIGURES_DIR, "convergence_windows.png"))
    plt.close(fig)


# ===========================================================================
# Figure 5: v2 Distribution
# ===========================================================================

def fig5_v2_distribution(results):
    """Grouped bar chart of v2 distribution for each k."""
    print("  Generating: v2_distribution.png")

    part2 = results["part2"]
    ks = sorted(int(k) for k in part2.keys())

    # Collect all v2 values that appear
    all_v2 = set()
    for k in ks:
        v2_dist = part2[str(k)]["v2_distribution"]
        for v in v2_dist:
            all_v2.add(int(v))
    v2_vals = sorted(all_v2)

    # Compute fractions (count / total odd residues)
    fractions_data = {}
    for k in ks:
        info = part2[str(k)]
        total = info["num_odd"]
        v2_dist = info["v2_distribution"]
        fracs = []
        for v in v2_vals:
            count = v2_dist.get(str(v), 0)
            fracs.append(count / total)
        fractions_data[k] = fracs

    # Theoretical geometric: 1/2^v2
    theoretical = [1.0 / (2 ** v) for v in v2_vals]

    fig, ax = plt.subplots(figsize=(12, 6))

    n_groups = len(v2_vals)
    n_bars = len(ks) + 1  # +1 for theoretical
    bar_width = 0.8 / n_bars
    x = np.arange(n_groups)

    colors_list = ["#1f77b4", "#ff7f0e", "#2ca02c", "#d62728", "#9467bd", "#8c564b"]

    for i, k in enumerate(ks):
        offset = (i - n_bars / 2 + 0.5) * bar_width
        ax.bar(x + offset, fractions_data[k], bar_width * 0.9,
               color=colors_list[i % len(colors_list)], alpha=0.8,
               label=f"$k={k}$", edgecolor="white", linewidth=0.5)

    # Theoretical line
    offset_theo = (len(ks) - n_bars / 2 + 0.5) * bar_width
    ax.bar(x + offset_theo, theoretical, bar_width * 0.9,
           color="black", alpha=0.3, label="$1/2^{v_2}$ (geometric)",
           edgecolor="black", linewidth=0.8, hatch="//")

    ax.set_xlabel("$v_2$ value")
    ax.set_ylabel("Fraction of odd residues")
    ax.set_title("$v_2$ Distribution Across Moduli\nCompared to Geometric $1/2^{v_2}$ Pattern",
                 fontweight="bold")
    ax.set_xticks(x)
    ax.set_xticklabels([str(v) for v in v2_vals])
    ax.legend(loc="upper right", framealpha=0.9, ncol=2, fontsize=9)
    ax.set_ylim(0, 0.65)
    ax.grid(axis="y", alpha=0.3)

    fig.savefig(os.path.join(FIGURES_DIR, "v2_distribution.png"))
    plt.close(fig)


# ===========================================================================
# Figure 6: Worst-case Drift Paths
# ===========================================================================

def find_worst_path(transitions, num_steps):
    """
    Find the starting residue that achieves maximum cumulative drift
    over num_steps steps, and return the full path with step-by-step drift.
    Uses DP with backtracking.
    """
    odd_residues = list(transitions.keys())

    # Forward DP: dp[w][r] = max cumulative drift over w steps starting at r
    # parent[w][r] = the successor used (always image(r), but we track for path)
    dp = [{r: Fraction(0) for r in odd_residues}]

    for w in range(1, num_steps + 1):
        dp_curr = {}
        for r in odd_residues:
            vv, image = transitions[r]
            d = Fraction(1585, 1000) - vv  # LOG2_3 approx - v2
            if image in dp[w - 1]:
                dp_curr[r] = d + dp[w - 1][image]
            else:
                dp_curr[r] = d
        dp.append(dp_curr)

    # Find the starting residue with max drift at step num_steps
    best_start = max(dp[num_steps], key=dp[num_steps].get)

    # Trace the path forward
    path = []
    cumulative_drifts = [0.0]
    node = best_start
    cumulative = 0.0
    for step in range(num_steps):
        vv, image = transitions[node]
        step_drift = LOG2_3_FLOAT - vv
        cumulative += step_drift
        path.append({
            "residue": node,
            "v2": vv,
            "step_drift": step_drift,
            "cumulative_drift": cumulative,
        })
        cumulative_drifts.append(cumulative)
        node = image

    return best_start, path, cumulative_drifts


def fig6_worst_case_paths(results):
    """Trace worst-case drift paths for k=3 and k=4."""
    print("  Generating: worst_case_paths.png")

    fig, axes = plt.subplots(1, 2, figsize=(14, 6), sharey=False)

    for idx, k_exp in enumerate([3, 4]):
        ax = axes[idx]
        modulus, transitions = build_transition_graph(k_exp)

        # Determine a good number of steps to trace -- use the convergence
        # window or 30, whichever is larger
        part3_k = results["part3"].get(str(k_exp), {})
        conv_w = part3_k.get("convergence_window")
        num_steps = max(30, conv_w + 10 if conv_w else 30)
        num_steps = min(num_steps, 40)

        best_start, path, cum_drifts = find_worst_path(transitions, num_steps)

        steps = list(range(num_steps + 1))

        # Color each segment by its v2
        for i in range(num_steps):
            v2_val = path[i]["v2"]
            color = edge_color_for_v2(v2_val)
            lw = 3 if v2_val == 1 else 2
            ax.plot([steps[i], steps[i + 1]],
                    [cum_drifts[i], cum_drifts[i + 1]],
                    "-", color=color, linewidth=lw, solid_capstyle="round")

        # Mark each point
        for i in range(num_steps):
            v2_val = path[i]["v2"]
            color = edge_color_for_v2(v2_val)
            ax.plot(steps[i + 1], cum_drifts[i + 1], "o", color=color,
                    markersize=4, zorder=5)

        ax.plot(0, 0, "s", color="black", markersize=6, zorder=6)

        # Zero line
        ax.axhline(y=0, color="black", linewidth=1, linestyle="--", alpha=0.5)

        # Highlight bad streak regions
        in_streak = False
        streak_start = None
        for i in range(num_steps):
            if path[i]["v2"] == 1:
                if not in_streak:
                    streak_start = i
                    in_streak = True
            else:
                if in_streak:
                    ax.axvspan(streak_start, i, alpha=0.08, color="red")
                    in_streak = False
        if in_streak:
            ax.axvspan(streak_start, num_steps, alpha=0.08, color="red")

        # Find max drift point
        max_drift_idx = max(range(len(cum_drifts)), key=lambda j: cum_drifts[j])
        ax.annotate(f"Peak: {cum_drifts[max_drift_idx]:.2f}",
                    xy=(max_drift_idx, cum_drifts[max_drift_idx]),
                    xytext=(max_drift_idx + 2, cum_drifts[max_drift_idx] + 0.5),
                    fontsize=9, fontweight="bold", color="darkred",
                    arrowprops=dict(arrowstyle="->", color="darkred", lw=1))

        ax.set_xlabel("Step number")
        ax.set_ylabel("Cumulative drift (bits)")
        ax.set_title(f"Worst-case Drift Path: $k = {k_exp}$\n"
                     f"(mod {modulus}, start residue {best_start})",
                     fontweight="bold")
        ax.grid(alpha=0.3)

        # Add v2 sequence annotation at bottom
        v2_seq = [str(p["v2"]) for p in path[:min(20, num_steps)]]
        v2_text = "v$_2$ seq: " + ",".join(v2_seq)
        if num_steps > 20:
            v2_text += "..."
        ax.text(0.02, 0.02, v2_text, transform=ax.transAxes,
                fontsize=7, verticalalignment="bottom",
                bbox=dict(boxstyle="round,pad=0.3", facecolor="wheat", alpha=0.7))

    # Shared legend
    legend_elements = [
        plt.Line2D([0], [0], color="#d62728", linewidth=3, label="v$_2$ = 1 (bad, drift +0.585)"),
        plt.Line2D([0], [0], color="#1f77b4", linewidth=2, label="v$_2$ = 2 (good, drift -0.415)"),
        plt.Line2D([0], [0], color="#2ca02c", linewidth=2, label="v$_2$ = 3+ (very good)"),
        mpatches.Patch(facecolor="red", alpha=0.1, label="Bad streak region"),
    ]
    fig.legend(handles=legend_elements, loc="lower center",
               ncol=4, fontsize=9, framealpha=0.9,
               bbox_to_anchor=(0.5, -0.02))

    fig.suptitle("Worst-case Drift Paths through Syracuse Transition Graph",
                 fontsize=14, fontweight="bold", y=1.02)
    plt.tight_layout()
    fig.savefig(os.path.join(FIGURES_DIR, "worst_case_paths.png"),
                bbox_inches="tight")
    plt.close(fig)


# ===========================================================================
# Main
# ===========================================================================

def main():
    setup_style()

    print("Loading results from:", RESULTS_PATH)
    results = load_results()

    print("Generating figures...")

    fig1_zmod13_transitions(results)
    fig2_zmod104_transitions(results)
    fig3_bad_streaks_vs_k(results)
    fig4_convergence_windows(results)
    fig5_v2_distribution(results)
    fig6_worst_case_paths(results)

    print(f"\nAll figures saved to: {FIGURES_DIR}/")
    print("Done.")


if __name__ == "__main__":
    main()

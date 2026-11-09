module

public import FrenMir.Walking

public section
namespace FrenMir

/-- No prefix selection: membership is exactly the full block's role filter. -/
theorem assumptions_exact (b : Block) (m : FrenModule.TypedBody) :
    m ∈ b.assumptions ↔ m ∈ b.members ∧ m.member.any (·.kind == .assume) = true := by
  simp [Block.assumptions]

theorem goals_exact (b : Block) (m : FrenModule.TypedBody) :
    m ∈ b.goals ↔ m ∈ b.members ∧ m.member.any (·.kind == .expect) = true := by
  simp [Block.goals]

/-- The satisfiability question always exists, even for empty blocks. -/
theorem satisfiability_first (b : Block) :
    b.requests[0]? = some ⟨b.owner, b.parameters, b.context, b.assumptions,
      .assumptionsSatisfiable, b.assumptions.map Demand.mk⟩ := by
  simp [Block.requests, Array.getElem?_append]

theorem request_count (b : Block) : b.requests.size = 1 + b.goals.size := by
  simp [Block.requests]

/-- A request cannot gain another block's context or another unproved goal as
an assumption. This law constrains the helper called by the real producer. -/
theorem request_context (b : Block) (r : CheckRequest) (h : r ∈ b.requests) :
    r.owner = b.owner ∧ r.parameters = b.parameters ∧ r.context = b.context ∧
      r.assumptions = b.assumptions := by
  simp only [Block.requests, Array.mem_append, Array.mem_singleton, Array.mem_map] at h
  rcases h with h | ⟨g, _, h⟩
  · subst r; exact ⟨rfl, rfl, rfl, rfl⟩
  · subst r; exact ⟨rfl, rfl, rfl, rfl⟩

/-- Exactly one validity entry per written goal, carrying its entire demand
root and all assumption demand roots. It does not discharge definedness. -/
theorem validity_member (b : Block) (g : FrenModule.TypedBody) (h : g ∈ b.goals) :
    (⟨b.owner, b.parameters, b.context, b.assumptions, .validity g,
      (b.assumptions.map Demand.mk).push ⟨g⟩⟩ : CheckRequest) ∈ b.requests := by
  simp only [Block.requests, Array.mem_append, Array.mem_map]
  exact Or.inr ⟨g, h, rfl⟩

end FrenMir

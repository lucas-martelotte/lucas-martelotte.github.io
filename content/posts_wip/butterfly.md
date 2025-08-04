---
title: One-line proof of Butterfly Lemma
subtitle: 
keywords: [diagrams, group-theory, relations]
date: 2025-06-29
description: ToDo
---

<!--
THEOREMS TO DO
- A, B normal in G => AB normal in G
- f sur, A normal in G => f(A) normal
-->


<!--
1) Group relations
2) Simple equations, sur, inj, etc, and the issue of normality
3) First isomorphism theorem of relations
4) The Butterfly Lemma 
-->

<!-- Some time ago me and some friends came up with a neat way to prove the Butterfly Lemma. This was, in fact, a big motivator for starting this blog. The main idea is that quotients are hard to work with, and the First Isomorphism Theorem allows us to avoid them. To be more precise, when trying to prove $A/B \cong C$, instead of working directly with the quotient $A/B$, it is enough to find some homomorphism $f$ such that

- $f$ has domain $A$;
- $f$ has kernel $B$;
- $f$ has image $C$.

Notice that none of these three tasks involve quotients! This simplification is almost second-nature to every group theorist. The problem with the Butterfly Lemma, however, is that it is an isomorphism in which both sides are quotients, i.e. something of the form $A/B \cong C/D$. The First Isomorphism Theorem can only save us from one of the quotients!

The good news is that, if one is willing to slightly broaden the definition of a function, it is possible to generalize the First Isomorphism Theorem to work with two quotients instead of just one.


Generalizing Functions
======================

A group homomorphism $f : A \rightarrow B$ can be thought of as a subgroup $F \subseteq A \times B$ satisfying the property that

- $\forall a \in A, \; \exists ! b \in B \;:\; (a,b) \in F$.

Let's forget this property from now on, and see where this new generality leads us. We define a **group relation** between $A$ and $B$ to be a subgroup of $A \times B$. Let's look at some examples.

- There are always two groups relations between any groups $A$ and $B$, namely the two trivial subgroups of $A \times B$.

- Given a group homomorphism $f : A \rightarrow B$, its graph $\{(x,y) \;:\; f(x) = y\} \subseteq A \times B$ defines a group relation between $A$ and $B$.

- If $A = B = \mathbb{Z}$, we have a group relation $\{(x,y) \;:\; x \equiv y \mod{2}\} \subseteq \mathbb{Z} \times \mathbb{Z}$.

There are two ways of composing group relations, which are called **parallel** and **direct** composition. In this post, we'll only need the latter, defined below.

<!-- - If $R \subseteq A_1 \times B_1$ and $S \subseteq A_2 \times B_2$ are two group relations, we define their **parallel sum** $R \times S \subseteq (A_1 \times A_2) \times (B_1 \times B_2)$ as $\{((x_1, x_2), (y_1, y_2)) \;:\;  (x_1, y_1) \in R \text{ and } (x_2, y_2) \in S\}$. -->

Recently I've been thinking about ways that relations and graphical languages can help one understand group theory. This turned out to be a very interesting side project, and I ended up finding a neat way to prove the [Butterfly Lemma](https://en.wikipedia.org/wiki/Zassenhaus_lemma). Sharing this proof was part of the reason I wanted to create this blog.

In this first part, I will attempt to give a rough crash course on relations. I say relations, and not *group* relations, because most of the things I'll talk about here work for almost any flavor of relation you might think of, be it ordinary relations between sets, linear relations, ring relations, monoid relations, module relations, you name it. Maybe there is a more profound, categorical reason for why this might be so, but for now it doesn't matter. Anyhow, many things may be skipped, or explained in an unsatisfactory way, but I encourage you to try and work it out yourself if you feel something is unjustified. I believe nothing that is written here is very laborous to work out. Any questions you might have, mistakes or typos you might find, please e-mail me!

# Part 1: Group relations

Given any two groups $G$ and $H$, a **group relation** $R$ between them is a subgroup $R \leq G \times H$. Notice we always have two trivial group relations between any two groups, namely the *full relation* $G \times H$ and the *empty relation* $\{(e_G, e_H)\}$, where $e_G$ and $e_H$ are, respectively, the neutral elements of $G$ and $H$. 

Given a group homomorphism $f : G \rightarrow H$, its graph $\text{Gr}(f) := \{(g, fg) \;:\; g \in G\}$ is a group relation between $G$ and $H$. (The converse also holds!) Also, any subgroup $G' \leq G$ can be thought of as the group relation $\{(e, g) \;:\; g \in G'\}$ between the trivial 1-element group $\{e\}$ and $G$.

Group relations can be composed in two different ways, called *direct* and *parallel* composition. The first one is defined as follows. Given group relations $S \leq G \times Z$ and $R \leq Z \times H$, their direct composition is
$$S ; R := \{(g, h) \;:\; \exists z \in Z, \; (g, z) \in S \text{ and } (z, h) \in R\} \leq G \times H.$$
Surprisingly so, group relations are closed by this funky definition. Not only that, but this is compatible with composition of functions, in the sense that
$$\text{Gr}(f ; g) = \text{Gr}(f) ; \text{Gr}(g),$$
or, in more fancy terms, the association $f \mapsto \text{Gr}(f)$ defines a (faithful) functor from the category of groups to the category of group relations, which even though I've not properly defined you might guess what it is.

The second form of composing relations, called parallel composition, is the analogue of the product of two maps. Given two relations $R_1 \leq G_1 \times H_1$ and $R_2 \leq G_2 \times H_2$, their parallel composition is a subgroup of $(G_1 \times G_2) \times (H_1 \times H_2)$ given by
$$R_1 \times R_2 := \{((g_1, g_2), (h_1, h_2)) \;:\; (g_1, h_1) \in R_1 \text{ and } (g_2, h_2) \in R_2\}.$$
Parallel composition of two graphs corresponds to the graph of the product of the corresponding maps, in other words, $\text{Gr}(f) \times \text{Gr}(g) = \text{Gr}(f \times g)$, where $f \times g$ is defined as $(x,y) \mapsto (fx, gy)$.

Direct and parallel composition satisfy a weird swapping rule
$$\begin{equation} (A \times C) ; (B \times D) = (A ; B) \times (C ; D). \end{equation}$$
This might look unintuitive for now, but when written in terms of string diagrams you will see that this rule is essentially associativity in disguise.

Another important operation on relations is called *opposite*, denoted $R^{\rm op}$, which simply amounts to swapping the two entries. More concretely, given a group relation $R \leq G \times H$, its opposite is
$$R^{\rm op} := \{(h, g) \;:\; (g, h) \in R\} \leq H \times G.$$

Once again, the opposite of a group relation is itself a group relation. When a homomorphism $f$ is invertible, the opposite of its graph is the graph of its inverse, i.e.
$$\text{Gr}(f)^{\rm op} = \text{Gr}(f^{-1}),$$
so, in a sense, opposite is a generalization of inverse.


## String diagrams

Now let's define some diagrams. An arbitrary relation $R$ between groups $G$ and $H$ will be depicted as the following string-diagram.
$$\text{Relation $R$}.$$
When there is no confusion to be made, the letters $G$ and $H$ above the wires will be omitted. Composing two group relations $S \leq G \times Z$ and $R \leq Z \times H$ amounts to plugging their wires in the correct order, i.e.
$$\text{Direct composition of diagrams},$$
whereas the parallel composition of two group relations $R_1 \leq G_1 \times H_1$ and $R_2 \leq G_2 \times H_2$ will be drawn as the vertical stacking of the two corresponding diagrams.
$$\text{Parallel composition of diagrams}.$$
This notation introduces the possibility of multiple dangling wires appearing in both sides of a group relation, but this is just a notation. The way to translate it back to the usual one-wired diagram is through the definition
$$\text{Wire of product is product of wires},$$
which, of course, allows for any number of dangling wires via induction.

In this language, notice that the swapping rule $(1)$ from earlier corresponds to the two ways in which one can parenthesize the following expression.
$$\text{Swapping rule in diagrams}.$$
Therefore, in a way, rule $(1)$ is a sort of 2D associativity law. Due to this, together with the fact that parallel and direct compositions are themselves associative as well, we will completely omit parentheses in all our future diagrams.

Lastly, the opposite of $R$ will be denoted by the same diagram, but horizontally inverted.
$$\text{Opposite of $R$}.$$


## Special relations

Now we will talk about some special kinds of group relations, that are so important so as to earn dedicated notations. First of all, given any relation $R$, we have seen how to draw its corresponding diagram as a chamfered box with wires sticking out of both sides. In the special case where $R$ is the graph of a homomorphism $f : G \rightarrow H$, we simply call it $f$ and its diagram will be drawn as the curvy node
$$\text{Graph of $f$}.$$
For any group $G$, we always have a special endomorphism called the indentity map $\text{id}_G$. In this specific case, since this is the *neutral element* of direct composition, we will draw it as the single dangling wire
$$\text{Identity}$$
to indicate that plugging it into anything produces no effect.

The relation corresponding to a subgroup $G' \leq G$ will be
$$\text{Relation of $G'$}.$$
In other words, the abscence of a left-wire indicates that the "domain" of the group relation is the trivial group. The two trivial subgroups of any group $G$, namely $G$ itself (the full subgroup) and $\{e_G\}$ (the empty subgroup), are very important and so will be given special designs.
$$\text{Trivial subgroups}.$$
You might already guess how the two trivial group relations from earlier, namely the full and empty relations, are drawn. They are just the composition of the full (resp. empty) subgroup with its opposite.
$$\text{Full and empty relations}.$$

Now we introduce two new group relations called **copy** and **sum**.
$$\text{Copy and sum}$$

The first one (**copy**) is simply the graph of the diagonal homomorphism $\Delta_G : G \rightarrow G \times G$ defined as $g \mapsto (g,g)$. The second one (**sum**) is the graph of the multiplication homomorphism $\nabla_G : G \times G \rightarrow G$ defined as $(g_1, g_2) \mapsto g_1g_2$.

Notice a problem? Things would be fine and dandy if not for the fact that $\nabla_G$ is not a homomorphism, unless $G$ is a commutative group! In fact, we must have the equality
$$g_2g_1 = \nabla_G(e_G, g_2) \nabla_G(g_1, e_G) = \nabla_G(g_1, g_2) = g_1g_2.$$

However, let's not discard it yet. Maybe it becomes a legitimate group relation if we compose it with something else. For example, let's try plugging in a subgroup $H \leq G$ to one of the left-wires of **sum**, and lets call it **sum**$_H$.
$$\text{Sum with subgroup}.$$

Now, what equation do we need to satisfy for this to be a group relation? Given any two elements $(g_1, h_1g_1)$ and $(g_2, h_2g_2)$ inside this set, we need $(g_1g_2, h_1g_1h_2g_2)$ to also be inside it. In other words, we must find some $h \in H$ such that
$$h_1g_1h_2g_2 = hg_1g_2.$$
We can absolutely do that if $H$ is a normal subgroup of $G$. The nice surprise is that the converse also holds! In other words, a subgroup $H \leq G$ is normal if and only if **sum**$_H$ is a group relation. Moreover, if that happens, it doesn't matter in which wire we plug $H$ in, i.e.
$$\text{Summing $H$ above or below is the same}.$$

This is, (very) informally speaking, our first example of a non-trivial group relation which doesn't come from a homomorphism. If group theory, as it is classicaly taught, were a lego set, where our lego pieces are groups and group homomorphisms, this would be a *new* type of piece we are only allowed to use when we broaden our view to group relations. And we will make good use of it. In fact, this will be crucial to proving the Butterfly Lemma later on.

# Part 2: The First Isomorphism Theorem

Maybe one of the most useful results in mathematics is the First Isomorphism Theorem. We mathematicians use it all the time, and most of the time we don't even notice we're using it. After I played a little bit with group relations, the first things that came to mind was what is the analogue of the First Isomorphism Theorem. The answer is quite satisfactory, but first we have to make sense of what *image* and *kernel* and *domain* mean in this world. This is not hard. In fact, we already have all the necessary pieces to construct them. Given any group relation $R$, we define
$$\text{Kernel, image and domain}.$$
These three naturally generalize the notions of kernel, image and domain for homomorphisms, in the same usual sense as before. The graphical notation, however, hints at one more construction which we didn't do yet, namely
$$\text{nil}.$$
This doesn't have a name yet, so let's name it *nil*. This one didn't come up before because the nil of any function is always the trivial subgroup. In fact, nil measures how *deterministic* a group relation $R \leq G \times H$ is: if nil is trivial, then for any element $g \in G$ there is *at most* one element $h \in H$ such that $(g, h) \in R$. It is the dual sense of the kernel, which measures how deterministic a group relation is on the opposite direction; for example, a function with non-trivial kernel has multiple pre-images of any element in its image. In fact, looking at nil as measuring determinancy is a very good thing to do. Let's set it in stone in the following definition.
$$\text{Injective, surjective, total and deterministic}.$$
I don't even have to say that the notions of injective and surjective match the corresponding notions for homomorphisms. But now we get two more: deterministic and total. We have already discussed the first one. Total means that for every element $g \in G$, there is *at least* one element $h \in H$ such that $(g, h) \in R$.

Question: what happens when we join deterministic with total? When we join *at least one* with *at most one* we get *exactly one*, so a relation $R \leq G \times H$ is total and deterministic if and only if for every $g \in G$ there is exactly one $h \in H$ such that $(g, h) \in R$. Well, that is exactly the definition of a function, isn't it? In fact, it is not hard to prove that
$$ R \text{ is total and deterministic} \iff R \text{ is the graph of a homomorphism.}$$
Moreover, as one might expect, if $R$ is total, deterministic, surjective and injective it must be the graph of an isomorphism. In the same way one can characterize injective and surjective homomorphisms. By combining these four properties in different ways we can arrive at other, more colorful constructions such as *allegories*. But this is a subject for another post.

We are now ready for the First Isomorphism Theorem for group relations. Let us state it in all its glory.

::: {.Theorem data-title="First Isomorphism Theorem"} 
Let  $R \leq G \times H$ be a group relation. Then, there is an isomorphism $$\frac{\text{Dom}(R)}{\text{Ker}(R)} \cong \frac{\text{Img}(R)}{\text{Nil}(R)}.$$
:::

Notice how, if $R$ is the graph of a homomorphism, the nil becomes trivial and we recover the usual theorem for functions. This beautiful generalization of the First Isomorphism Theorem is, in fact, a known theorem in disguise: [Goursat's Lemma](https://en.wikipedia.org/wiki/Goursat%27s_lemma). The statement, as it is written on wikipedia, is quite nasty, but when properly parsed it says essentially the same thing as the theorem above. This, in my humble opinion, is good example where relations can be used to clean up mathematics.

# Part 3: The Butterfly Lemma

Our last goal today is to use everything we have discussed so far in order to prove the Butterfly Lemma.
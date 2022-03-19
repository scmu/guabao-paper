% build using
%    lhs2TeX GuabaoPaper.lhs | pdflatex --jobname=GuabaoPaper

\documentclass[runningheads]{llncs}

%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt
%include Formatting.fmt
%include GCL.fmt

\include{macros}

\begin{document}

\title{Imperative Program Derivation in Guabao
%\thanks{Supported by organization x.}
}

\author{Shin-Cheng Mu\inst{1}%\orcidID{0000-0002-4755-601X}
\and
Ting-Yan Lai\inst{1}\and
Thing-Han Lim\inst{1}}
%
\authorrunning{S-C. Mu  et al.}

\institute{
Institute of Information Science, %\\
Academia Sinica, Taiwan}


\maketitle              % typeset the header of the contribution
%
\begin{abstract}
The abstract should briefly summarize the contents of the paper in
150--250 words.

\keywords{program derivation \and integrated developing environment \and proofs}
\end{abstract}

\section{Introduction}

\begin{quote}
\ldots to prove the correctness of a given program was in a sense putting the cart before the horse. A much more promising approach turned out to be letting correctness proof and program grow hand in hand: with the choice of the structure of the correctness proof one designs a program for which this proof is applicable. The fact that then the correctness concerns turn out to act as an inspiring heuristic guidance is an added benefit.
\begin{flushright}
--- E. W. Dijkstra, 1973. \cite{Dijkstra:74:Programming}
\end{flushright}
\end{quote}

\emph{Program derivation} is the process of formally and step-wise constructing a program from its specification, such that every step is mathematically justifiable. As a methodology to construct reliable software, its central idea is that, rather than verifying a program after it has been written, \emph{a program and its correctness proof should be developed hand in hand}.
This does not necessarily imply more work for the programmer.
On the contrary, as argued in the quote above, thinking about how a program can be proven correct once it is written often gives useful hints on how to construct the program.

Theories of imperative program derivation was initially developed by Dijkstra~\cite{Dijkstra:75:Guarded}, based on the \emph{weakest precondition} calculus. It can be seen as a variation of Hoare logic~\cite{Hoare:69:Axiomatic} where, instead of a more conventional operational semantics, the meaning of a program is taken to be a predicate transformer: a function that, given a desired postcondition $Q$, yields the weakest precondition $P$ such that the program would terminate in a state that satisfies $Q$. This view of programs invites the programmer to abstract away from how the program operationally carries out its task, and instead to focus on what the programmer wants to achieve and to derive a program achieving the post condition by various calculational rules.
Various previous work~\cite{Dijkstra:76:Discipline,%
Gries:81:Science,Kaldewaij:90:Programming,Morgan:90:Programming,%
Backhouse:03:Program,Backhouse:11:Algorithmic} collectively developed a methodology of program development from specification: how to construct a loop invariant from a desired postcondition; how to construct the loop body from its last step; how to ensure termination, etc.
This methodology was applied to derive algorithms
solving individual small problems
(e.g~\cite{Rem:89:Small,Rem:90:Small}) as well as families of problems (e.g~\cite{Zantema:92:Longest}).
Meanwhile, derivation of functional programs, a closely related topic, has also been developing (e.g~\cite{Bird:10:Pearls}).
Within the advocating community it is at least wished that the concept of program derivation should be taught as part of the fundamental training for programmers and computing science majors.
% These days, program derivation is more practiced in the functional programming community. Derivation of imperative programs, however, is also a field with rich possibilities and potentials.

Since 2011, the first author has been teaching an undergraduate level Programming Languages course, in which imperative program derivation is covered.
From the experiences accumulated, we felt that such a course would benefit from having a supporting tool.
Therefore we created Guabao,
developed tool aims to be both for teaching and for algorithm construction.

\section{Motivation}
\label{sec:motivation}

Derivation of functional programs is relatively linear. We start from a specification, transform it to the next, until we have a program whose performance we are happy about.
Shown below is an outline derivation of the classical ``maximum segment sum'' (MSS) problem --- that is, given a list of numbers, compute the largest sum of a consecutive segment:
\begin{spec}
   maximum . map sum . concat . map inits . tails  -- problem specification
=    {- since |map f . concat = concat . map (map f)| -}
   maximum . concat . map (map sum) . map inits . tails
=    {- other properties -}
   ...
=    {- more properties -}
   maximum . scanr oplus 0 {-"~~."-}               -- a faster program
\end{spec}
The problem specification in the first line is a functional program that exhaustively generates all segments, computes the sums for each of them, and picks the maximum.
The point here is not the technical details but the style.
The derivation is a consecutive, long chunk of calculation proof.
Properties needed (such as |map f . concat = concat . map (map f)|) can be proved as a separate lemma, and when we do so, its relationship to the main proof is clear.
If the derivation does not work, we may realise (by inspecting what is missing in the derivation) that we need to start from a more general specification.
We then construct the new specification, and start over again.
All these proceed in a way similar to doing mathematical proofs on a piece of paper, from top of the page to the bottom.
In fact, such derivations was indeed often carried out on paper.

Not having proper tools, derivations of imperative programs were also mostly carried out on paper. However, the experience is less linear and much more messy -- it is more like keeping writing and erasing symbols on a white board.
Consider also the MSS problem, where the input is an array |A| of |N| integers.
One might expect that the problem will be solved using a loop.
In the \emph{Guarded Command Language}~\cite{Dijkstra:75:Guarded} a while-loop (with a single body) is denoted by:
\begin{spec}
htriple (P, bnd: e) (DO B -> S OD) Q
\end{spec}
where |P| is the loop invariant, |e| the \emph{bound} (a value that strictly decreases after each iteration of the loop), and |Q| the postcondition.
When the \emph{guards} |B|, the command |S| is executed and the loop gets iterated again; otherwise the loop exits.

Once we introduce a loop, however, we have also gave ourselves \emph{four} proof obligations:
\begin{enumerate}
\item |P && not B ==> Q|,
\item |htriple (P && B) S P|,
\item |P && B ==> e >= 0|,
\item |htriple (P && B && e = C) S (e < C)|.
\end{enumerate}
The first two properties guarantee that the loop is partially correct: that is, if the loop terminates at all, it terminates in a state satisfying |Q|. The last two properties establishes that the loop actually terminates. The four properties together guarantee total correctness.
Often, one or two of the properties are rather trivial.
Still, they need to be proved.

For the MSS problem we may choose |Q <=> (s = mss N)|, where
|mss n = maxquant (p q) (0 <= p <= q <= n) (sum p q)|, the maximum sum of all segments in |arrayCO A 0 n|, and |sum p q| computes the sum of |arrayCO A p q|.
A common strategy is to establish the postcondition using a loop in which we keep increment a variable |n| until it reaches |N|. Therefore we come up with the following program skeleton:
\begin{spec}
s,n := 0,0
(assert (s = mss n, bnd: N-n))
DO n /= N ->  [:  s = mss n && n /= N,
                  s = mss (n + 1) :]
              n := n + 1
OD
(assert (s = mss N))  {-"~~,"-}
\end{spec}
where
|[: pre, post :]| denotes a \emph{spec} --- a piece of program yet-to-be-finished that is supposed to establish postcondition |post| given precondition |pre|.

% Transition from the previous program to this one is like tweaking expressions on a white board.
To further refine the specification, one may try to find a way to efficiently update |s|. It will turn out that this can only be done by introducing an auxiliary variable:
\begin{spec}
s,n := 0,0
(assert (s = mss n && t = msf n, bnd: N-n))
DO n /= N ->  [:  s = mss n && t = msf n && n /= N,
                  s = mss (n + 1) && t = msp (n +1) :]
              n := n + 1
OD
(assert (s = mss N))  {-"~~,"-}
\end{spec}
where |msf n| denotes the maximum sum of \emph{suffixes} of |arrayCO A 0 n|.

Once we introduce |t|, the four proof obligations are also updated accordingly and need to be proved again.

Finally, to prove termination, one may realise that we need additional constraints on |n|: |0 <= n <= N|. This again changes our proof obligations.

Development of an imperative program is like scribbling on a whiteboard, where the programmer may make changes here and there. The required proof obligations updates accordingly. The challenge of the programmer is to come up with the program, while making sure that all the proofs to be done are possible. When doing the proof, the programmer may realise that the program may need further generalisation to make the proof possible at all (it is in the spirit of Dijkstra’s methodology, that proofs and programs should be developed hand-in-hand).

It is certainly error-prone keeping track of all these proofs. When teaching, it is hard to give students a systematic idea what proofs are involved. A tool thats keeps track of all the proof obligations would be a much clearer and systematic presentation of the technique. Outside the classroom, such a tool would be helpful for experimenting with different strategies for developing algorithms. The developing environment could also employ external tools, such as a theorem prover or an SMT solver, to discharge the proof obligations.


\section{Programming in Guabao}
\label{sec:programming-example}

\cite{Runge:19:Tool}
\cite{Dijkstra:98:Cruelty}

\subsubsection{Acknowledgements} Please place your acknowledgments at
the end of the paper, preceded by an unnumbered run-in heading (i.e.
3rd-level heading).


%% Bibliography
\bibliographystyle{splncs04}
\bibliography{guabao}
%\input{LongParens.bbl}

\end{document}

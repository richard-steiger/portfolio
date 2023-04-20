# My Portfolio

This repo contains samples of my work products generated over the last 45 years, for the purpose of enabling evaluation of the breadth and depth of projects I frequently work on.

All of these artifacts are either my own IP, or are from client engagements or jobs where the projects were terminated by the client, have been published elsewhere, or have been suitably redacted, so can be shared without conflict.

You've been granted access to this repo for a limited time, purely for your reading and evaluation, hence the artifacts should not be cloned nor shared with others, and I would appreciate if you treat this as a private communication.

It's divided into 3 sections by artifact type.

## documents

- _Anyone's Guide To Conversation Service_ - architectural and functional design for an integrated repository for recording and analyzing conversations and their NLP events.
- _BPMEngineConcepts_ - high-level architectural and functional design of a workflow engine component, supporting modeling and tracking of business processes in Microsoft IT's massive supply chain system.
- _Position Paper: Making Our Products Modular_ - very early-stage analysis of technology challenges and proposed solution faced by client rapidly growing through acquisitions, and faced with massive integration requirements.
- _PDOM Functional Specification_ - functional specification for the Persistent Distributed Object Manager, a Smalltalk-80 package that replicated objects, transactions, queries, database management, and other computational assets, operations, and resources across geographically-distributed Smalltalk Virtual Machines.
- _Modular Platform Proposal_ - proposal to adopt more powerful higher-order data and operation semantics in an event processing system, in order to radically simplify code, and improve overall stability.
- _TheProblemsWithJava_ - notes about the more serious problems with the Java language architecture and implementation, and exploration of workarounds and extensions to the language and ecosystem.

## code

A couple of sample class definition files from _EWorks_, a proprietary application platform (out of about 7000 files containing 1.5 million LOC), to give a taste of my coding style, including fluent commenting, attention to readability, clear naming, strict source file structuring, and Smalltalk-style method grouping, all intended to maximize readability:

- _Type.java_ - the base-class for the platform's type system, which spans full lifecycle, specifically exists at runtime in development, staging, and production environments, yielding massive advantages over Java's massive _type erasure_ mistake.

* _MetaEntity.java_ - the core metadata underlying _EWorks_'s foundational entity architecture.

## legal

- _CounteringPersistencePatents_for_SunMicrosystems_ - study done for Sun Microsystems to counter an IP litigation by Persistent Software, essentially invalidating Persistent's patent claims.

# soc-fw-load

The file F_alu.als contains an implementation in Alloy of the protocol "F_alu" from the paper "Security of SoC firmware load protocols" by S. Krstić, J. Yang, D. W. Palmer, R. B. Osborne and E. Talmor, recovering the authors' example of a security flaw in the protocol (Figure 7, originally found using a Murphi implementation). The file F_alu-theme.thm contains an Alloy theme to aid in visualization of the dangerous trace, while the fifo.als and fifo-theme.thm files contain code for implementing and visualizing a circular FIFO in Alloy.

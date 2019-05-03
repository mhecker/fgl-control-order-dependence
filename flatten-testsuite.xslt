<xsl:stylesheet xmlns:sql="http://saxon.sf.net/sql" xmlns:xsl="http://www.w3.org/1999/XSL/Transform" version="1.0" xmlns:saxon="http://saxon.sf.net/" extension-element-prefixes="saxon sql">

<xsl:template match="/testsuites/@*">
    <xsl:copy>
        <xsl:apply-templates select="@*|node()" />
    </xsl:copy>
</xsl:template>

<xsl:template match="/testsuites">
    <testsuite>
        <xsl:apply-templates select="@* | node()" />
    </testsuite>
</xsl:template>

<xsl:template match="//testsuite[not(testsuite)]">
  <xsl:copy-of select="node()"/>
</xsl:template>

</xsl:stylesheet> 